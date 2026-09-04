const {
  consentFormId,
  apiUrl,
  submitApiUrl,
  signatureServiceUrl,
  showButtons,
  showLanguageDropdown,
  enableCheckboxes,
  enableRadioButtons,
  enableDropdowns,
  tenantToken,
  customAttributes,
  receivedType,
  customHeaders
} = window.consentWidgetConfig;

let createConsentRequestList = [];
let dataPrincipalIdList = [];
let clickEvent = function () {};
let consentJwt = null;

const urlParams = new URLSearchParams(window.location.search);

const campaignId = urlParams.get("c");
const linkToken = urlParams.get("lt");

const campaignLinkContext = {
  ...(campaignId && { campaignId }),
  ...(linkToken && { linkToken })
};


function authHeaders() {
  return {
    "Content-Type": "application/json",
    "Authorization-SDP": tenantToken || "",
        ...customHeaders
  };
}


async function handleApiResponse(res) {
  let payload = {};

  try {
    payload = await res.json();
  } catch (e) {
    payload = {};
  }

  const apiMessage =
    payload?.statusMessage ||
    payload?.message ||
    payload?.error?.message ||
    payload?.error;

  const isUnauthorized =
    res.status === 401 ||
    payload?.statusCode === 401;

  if (isUnauthorized) {
    const message = apiMessage || "401 UNAUTHORIZED";

    showApiMessageOnly(message);

    throw new Error(message);
  }

  // API returned an error HTTP status
  if (!res.ok) {
    const message =
      apiMessage ||
      `Request failed (${res.status})`;

    showApiMessageOnly(message);

    throw new Error(message);
  }

  return payload;
}

function showApiMessageOnly(message) {
  const widgetContainer = document.querySelector(".widget-container");

  if (!widgetContainer) return;

  widgetContainer.innerHTML = "";

  const error = document.createElement("div");
  error.className = "error-only-message";
  error.textContent = message || "";

  widgetContainer.appendChild(error);
}


// ── IndexedDB helper ──
let storedSigning = { bss: null, bssPublicKey: null, sss: null };
let pendingSignController = null;
let currentSnapshot = null;

const AES_KEY_B64 = "el+1+epeGlCquCYLsk3zyQTsq3KUKQKL9QcV0B9KIS8=";
let globalSSS = null;

function uint8ToBase64(bytes) {
  const chunkSize = 0x8000;
  let binary = "";

  for (let i = 0; i < bytes.length; i += chunkSize) {
    binary += String.fromCharCode.apply(
      null,
      bytes.subarray(i, i + chunkSize)
    );
  }

  return btoa(binary);
}

async function encryptPayload(body) {
  const keyBytes = Uint8Array.from(atob(AES_KEY_B64), c => c.charCodeAt(0));
  const cryptoKey = await crypto.subtle.importKey("raw", keyBytes, "AES-GCM", false, ["encrypt"]);
  const iv = crypto.getRandomValues(new Uint8Array(12));
  const encoded = new TextEncoder().encode(JSON.stringify(body));
  const cipher = await crypto.subtle.encrypt({ name: "AES-GCM", iv }, cryptoKey, encoded);
  const combined = new Uint8Array(iv.byteLength + cipher.byteLength);
  combined.set(iv, 0);
  combined.set(new Uint8Array(cipher), iv.byteLength);
  return uint8ToBase64(combined);
}
function openDB() {
  return new Promise((resolve, reject) => {
    const req = indexedDB.open("consent-signing-store", 2);
    req.onupgradeneeded = function(e) {
      const db = e.target.result;
      if (!db.objectStoreNames.contains("keys")) db.createObjectStore("keys");
    };
    req.onsuccess = e => resolve({
      put: (store, val, key) => new Promise((res, rej) => {
        const tx = e.target.result.transaction(store, "readwrite");
        const r = tx.objectStore(store).put(val, key);
        r.onsuccess = () => res(); r.onerror = () => rej(r.error);
      }),
      get: (store, key) => new Promise((res, rej) => {
        const tx = e.target.result.transaction(store, "readonly");
        const r = tx.objectStore(store).get(key);
        r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error);
      }),
    });
    req.onerror = () => reject(req.error);
  });
}

// Generates ECDSA P-256 key pair on first load; private key is non-extractable
// and stored in IndexedDB. Public key is exported as SPKI base64.
async function initSigningKey() {
  try {
    const db = await openDB();
    const existing = await db.get("keys", "signingKeyEC");
    if (existing) return;

    const keyPair = await crypto.subtle.generateKey(
      { name: "ECDSA", namedCurve: "P-256" },
      false,
      ["sign", "verify"]
    );

    await db.put("keys", keyPair.privateKey, "signingKeyEC");

    const pubKeyBuffer = await crypto.subtle.exportKey("spki", keyPair.publicKey);
    const pubKeyB64 = btoa(String.fromCharCode(...new Uint8Array(pubKeyBuffer)));
    await db.put("keys", pubKeyB64, "signingPublicKeyB64");
  } catch (e) {
    console.error("Signing key initialization failed:", e);
  }
}

async function getPublicKeyB64() {
  try {
    const db = await openDB();
    return await db.get("keys", "signingPublicKeyB64");
  } catch (e) {
    return null;
  }
}

// Produces canonical JSON (sorted keys, no whitespace) matching Go's canonicalize.
function canonicalizePayload(obj) {
  if (Array.isArray(obj)) {
    return "[" + obj.map(canonicalizePayload).join(",") + "]";
  }
  if (obj !== null && typeof obj === "object") {
    var keys = Object.keys(obj).sort();
    return "{" + keys.map(function(k) {
      return JSON.stringify(k) + ":" + canonicalizePayload(obj[k]);
    }).join(",") + "}";
  }
  return JSON.stringify(obj);
}

// Signs the payload using ECDSA-P256; returns base64url IEEE P1363 signature.
async function signPayload(payload) {
  try {
    const db = await openDB();
    const privateKey = await db.get("keys", "signingKeyEC");
    if (!privateKey) return null;

    const encoded = new TextEncoder().encode(canonicalizePayload(payload));
    const sigBuffer = await crypto.subtle.sign(
      { name: "ECDSA", hash: "SHA-256" },
      privateKey,
      encoded
    );
    return btoa(String.fromCharCode(...new Uint8Array(sigBuffer)))
      .replace(/[+]/g, "-").replace(/[/]/g, "_").replace(/=/g, "");
  } catch (e) {
    console.error("Payload signing failed:", e);
    return null;
  }
}

// Converts ASN.1 DER ECDSA signature (Go output) to IEEE P1363 (WebCrypto input).
function derToP1363(der) {
  var off = 2;
  if (der[1] === 0x81) off = 3;
  off++;
  var rLen = der[off++];
  var rPad = (rLen === 33 && der[off] === 0x00) ? 1 : 0;
  var rBytes = der.slice(off + rPad, off + rLen);
  off += rLen;
  off++;
  var sLen = der[off++];
  var sPad = (sLen === 33 && der[off] === 0x00) ? 1 : 0;
  var sBytes = der.slice(off + sPad, off + sLen);
  var result = new Uint8Array(64);
  result.set(rBytes.slice(-32), 32 - Math.min(rBytes.length, 32));
  result.set(sBytes.slice(-32), 64 - Math.min(sBytes.length, 32));
  return result;
}

// Verifies the server-side ECDSA-SHA256 signature against the payload.
async function verifySSS(payload, sssBase64Url, pemPublicKey) {
  try {
    let b64 = pemPublicKey
      .replace(/-----BEGIN PUBLIC KEY-----/g, '')
      .replace(/-----END PUBLIC KEY-----/g, '')
      .replace(/\s+/g, '')
      .replace(/[^A-Za-z0-9+/=]/g, '');


    while (b64.length % 4 !== 0) {
        b64 += '=';

        }
    var der = Uint8Array.from(atob(b64), function(c) { return c.charCodeAt(0); });
    var pubKey = await crypto.subtle.importKey("spki", der, { name: "ECDSA", namedCurve: "P-256" }, false, ["verify"]);

    var data = new TextEncoder().encode(canonicalizePayload(payload));
    var sigB64 = sssBase64Url.replace(/-/g, "+").replace(/_/g, "/");
    while (sigB64.length % 4) sigB64 += "=";
    var derBytes = Uint8Array.from(atob(sigB64), function(c) { return c.charCodeAt(0); });

    var p1363 = derToP1363(derBytes);

    var result = await crypto.subtle.verify({ name: "ECDSA", hash: "SHA-256" }, pubKey, p1363, data);

    return result;
  } catch (e) {
    console.error("[SDP-SIGN] verifySSS: exception:", e);
    return false;
  }
}

// Called on every radio/checkbox/dropdown change.
// Generates BSS, calls sdp-consent-signature, verifies SSS, stores result.
async function onSelectionChange(selectedLang) {

  const request = buildFinalConsentRequest(selectedLang);

  // Always track the latest snapshot so stale in-flight responses fail verification.
  currentSnapshot = request;
  var bssPublicKey = await getPublicKeyB64();
  var bss = await signPayload(currentSnapshot.createConsentRequestDtoWrapper);
  if (!bss || !bssPublicKey) { console.warn("[SDP-SIGN] onSelectionChange: BSS generation failed"); return; }

  try {
    var headers = { "Content-Type": "application/json" };
    var res = await fetch(signatureServiceUrl + "/v1/sign", {
      method: "POST",
  headers: headers,
      body: JSON.stringify({ payload: currentSnapshot.createConsentRequestDtoWrapper, bss: bss, bss_pkey: bssPublicKey })
    });
    if (!res.ok) {
      var signErr = null;
      try { signErr = await res.json(); } catch (e) {}
      if (res.status === 401) showToast(" 401 Unauthorized", "error");
      else if (res.status === 404) showToast(" 404 Not Found", "error");
      else if (res.status === 500) showToast(" 500 Service Down", "error");
      else if (signErr?.error?.code === "BSS_VERIFICATION_FAILED") showToast(" BSS authentication failed", "error");
      else if (signErr?.error?.code === "SSS_VERIFICATION_FAILED") showToast(" SSS authentication failed", "error");
      else showToast(" Signature service failed", "error");
      console.warn("[SDP-SIGN] Signature service returned", res.status);
      return;
    }
    var signData = await res.json();
    var sss = signData.sss;
    globalSSS = sss;
    
    // Verify against currentSnapshot (latest) — if user changed selection while
    //this request was in-flight, currentSnapshot !== snapshot and verification fails.
    var valid = await verifySSS(currentSnapshot.createConsentRequestDtoWrapper, sss, signData.sss_pkey);

    const submitBtn = document.getElementById("submitBtn");
    if (valid) {
      //storedSigning = { bss: bss, bssPublicKey: bssPublicKey, sss: sss };
      if (submitBtn) submitBtn.disabled = false;
    } else {
      if (submitBtn) submitBtn.disabled = true;
    }
  } catch (e) {
    console.error("[SDP-SIGN] Signature service call failed:", e);
    showToast("Signature service unavailable", "error");
  }
}


function buildFinalConsentRequest(selectedLang) {
  setDataPrincipalIdList();

  const requestList = [];
  const consentDiv = document.getElementById("consent-root");

    consentDiv.querySelectorAll(".permission-block").forEach(block => {

      const permissionNode = block.querySelector("[data-translate-text]");
      const permissionId = permissionNode && permissionNode.getAttribute("data-translate-text");

      if (!permissionId) {
          return;
      }

      requestList.push({
          consentLanguage: selectedLang,
          consentReceivedType: receivedType,
          customAttributes,
          dataPrincipalIdList,
          permissionId,
          optedForIndexes: []
      });
  });

  const checkedCheckboxes = Array.from(consentDiv.querySelectorAll('input[type="checkbox"]:checked'));
  const regularCheckboxes = checkedCheckboxes.filter(cb => !cb.closest(".ms-dropdown"));
  const multiselectCheckboxes = checkedCheckboxes.filter(cb => cb.closest(".ms-dropdown"));
  const radioButtons = consentDiv.querySelectorAll('input[type="radio"]:checked');
  const dropdowns = consentDiv.querySelectorAll("select");

  const pushConsent = (permissionId, optionId) => {
    let existing = requestList.find(r => r.permissionId === permissionId);

    if (existing) {
      existing.optedForIndexes.push(parseInt(optionId));
    } else {
      requestList.push({
        consentLanguage: selectedLang,
        consentReceivedType: receivedType,
        customAttributes,
        dataPrincipalIdList,
        permissionId,
        optedForIndexes: [parseInt(optionId)]
      });
    }
  };

  regularCheckboxes.forEach(cb => {
    if (!enableCheckboxes) return;
    if (!cb.name) return;
    pushConsent(cb.name, cb.getAttribute("data-option-id") || "0");
  });

  multiselectCheckboxes.forEach(cb => {
    if (!enableDropdowns) return;

    const msDropdown = cb.closest(".ms-dropdown");
    const permId = msDropdown && msDropdown.getAttribute("data-perm-id");
    const optionId = cb.getAttribute("data-option-id");

    if (!permId || optionId === null) return;
    pushConsent(permId, optionId);
  });

  radioButtons.forEach(rb => {
    if (!enableRadioButtons) return;
    pushConsent(rb.name, rb.getAttribute("data-option-id") || "0");
  });


  dropdowns.forEach(sel => {
    if (!enableDropdowns) return;

    // Skip "Select options"
    if (!sel.value) return;

    const opt = sel.options[sel.selectedIndex];
    const optionId = opt.getAttribute("data-option-id");

    if (optionId !== null) {
      pushConsent(sel.name, optionId);
    }
  });

  return {
    createConsentRequestDtoWrapper: requestList
  };
}
 

async function fetchConsentData(selectedLang) {
  try {
    const body = { consentFormId, ...campaignLinkContext};
    const publicKey = await getPublicKeyB64();
    if (publicKey) body.bssk = publicKey;
    const browserSignature = await signPayload({ consentFormId });

    const res = await fetch(apiUrl, {
      method: "POST",
      headers: authHeaders(),
      credentials: "include",
      body: JSON.stringify(body)
    });

    const result = await handleApiResponse(res);

    consentJwt = result.response.payload;
    const decoded = decodeJwt(consentJwt);
	  
    const payloadEncryptionEnabled = decoded.data.response.payloadEncryptionEnabled;
    window.payloadEncryptionEnabled = payloadEncryptionEnabled;
    
    const data =
      decoded?.data?.response?.data?.response?.[0] ||
      decoded?.data?.response?.[0] ||
      decoded?.response?.[0];

    if (!data) {
      document.getElementById("consent-root").innerText =
        "Consent data not found.";
      return;
    }

    // IMPORTANT: always re-render using selectedLang
    const lang =
        selectedLang?.toLowerCase() ||
        data.languages?.[0]?.toLowerCase() ||
        "en";

    renderConsent(data, lang);

    // Trigger initial signing so Submit button is enabled on page load
    await onSelectionChange(lang);
} catch (e) {
  const message = e?.message;

  if (message) {
    showApiMessageOnly(message);
  }
}
}

document.addEventListener("DOMContentLoaded", () => {
  const container = document.querySelector(".widget-container");

  if (!container) return;

  Array.from(container.children).forEach((child) => {
    if (!child.classList.contains("preview-statements")) {
      child.style.display = "none";
    }
  });

  const consentRoot = document.getElementById("consent-root");

  if (consentRoot) {
    consentRoot.innerText = "Loading...";
  }
});


function setDataPrincipalIdList() {
  dataPrincipalIdList = [];
  const { dataPrincipalId } = window.consentWidgetConfig || {};
  if (Array.isArray(dataPrincipalId)) {
    dataPrincipalId.forEach(({ key, value }) => {
      if (key && value) {
        dataPrincipalIdList.push({ key, value });
      }
    });
  }
}

function showToast(message, type) {
  const toast = document.getElementById("toast");
  if (!toast) return;

  toast.textContent = message;
  toast.style.backgroundColor =
    type === "success" ? "#4CAF50" : "#f44336";

  toast.style.visibility = "visible";
  toast.classList.remove("show"); 
  void toast.offsetHeight;        
  toast.classList.add("show");

  setTimeout(() => {
    toast.classList.remove("show");
    toast.style.visibility = "hidden";
  }, 3000);
}

function getFormValues(selectedLang) {
  const finalPayload = buildFinalConsentRequest(selectedLang);
  createConsentRequestList = finalPayload.createConsentRequestDtoWrapper;
  sendConsent();
}

async function sendConsent() {
  //setFormDisabled(true);
  try {
    
    const body = {createConsentRequestDtoWrapper: createConsentRequestList,...campaignLinkContext};
    if (storedSigning.bss) {
      body.bss = storedSigning.bss;
      body.sss = globalSSS;
      body.jwt = consentJwt;
    } else {
      const browserSignature = await signPayload(createConsentRequestList);
      if (browserSignature) body.bss = browserSignature;
        body.sss =globalSSS ;
	      body.jwt = consentJwt;
    }

    let requestBody;

    if (window.payloadEncryptionEnabled) {

        const encryptedPayload = await encryptPayload(body);

        requestBody = {
            payload: encryptedPayload
        };

    } else {

        requestBody = body;
    }

    const res = await fetch(submitApiUrl, {
        method: "POST",
        credentials: "include",
        headers: authHeaders(),
        body: JSON.stringify(requestBody)
    });

    const data = await res.json();
    try {
      sessionStorage.setItem("consentResponse", JSON.stringify(data));
    } catch (e) {
      console.error("Storage failed:", e);
    }

    if (data.response && data.statusCode === 200) {
    showToast("Consent saved successfully!", "success");

    await new Promise(resolve => setTimeout(resolve, 3000));

    const langSelect = document.getElementById("langSelect");
    const selectedLang =
      langSelect?.value ||
      document.documentElement.lang ||
      "en";

    await fetchConsentData(selectedLang);

    return data;
}


  } catch (err) {
    console.error(err);
    showToast("Failed to submit. Please check your network connection.", "error");
    throw err;

  } finally {
    // Send response to Android WebView if available
    if (typeof window.AndroidBridge !== 'undefined' && 
        typeof window.AndroidBridge.onApiResponse === 'function') {
      try {
        window.AndroidBridge.onApiResponse(JSON.stringify(data));
      } catch (error) {
        console.error('Failed to send response to Android:', error);
      }
    }
    setFormDisabled(false);
  }
}

function resetWidget(reSign = false) {
  const root = document.getElementById("consent-root");

  const inputs = root.querySelectorAll("input, select, textarea");
  inputs.forEach(el => {
    if (el.type === "checkbox" || el.type === "radio") {
      el.checked = false;
    } else {
      el.value = "";
    }
  });

  root.querySelectorAll(".ms-dropdown").forEach(ms => {
    const chips = ms.querySelector(".ms-chips");
    const placeholder = ms.querySelector(".ms-placeholder");
    if (chips) chips.innerHTML = "";
    if (placeholder) placeholder.style.display = "inline";
  });

  const submitBtn = document.getElementById("submitBtn");
  if (submitBtn) submitBtn.disabled = true;

  currentSnapshot = null;
  createConsentRequestList = [];
  globalSSS = null;

  if (reSign) {
    const langSelect = document.getElementById("langSelect");
    if (langSelect) {
      onSelectionChange(langSelect.value);
    }
  }
}

function setFormDisabled(disabled = true) {
  const root = document.getElementById("consent-root");
  const inputs = root.querySelectorAll("input, select, textarea, button");
  inputs.forEach(input => input.disabled = disabled);

  const submitBtn = document.getElementById("submitBtn");
  const cancelBtn = document.getElementById("cancelBtn");
  
  if (disabled) {
    submitBtn.classList.add("loading");
  } else {
    submitBtn.classList.remove("loading");
  }
}

function renderConsent(data, selectedLang) {

  // Show widget after successful API response
  const container = document.querySelector(".widget-container");

  if (container) {
    Array.from(container.children).forEach((child) => {
      child.style.display = "";
    });
  }

  const root = document.getElementById("consent-root");
  root.replaceChildren();

  const branding = data.branding || {};

  let permissions = [];
  if (Array.isArray(data.consentForm)) {
    permissions = data.consentForm.flatMap(cf => cf.permissions || []);
  } else if (Array.isArray(data.permissions)) {
    permissions = data.permissions;
  }

  const logoArea = document.getElementById("logo-area");
  logoArea.innerHTML = "";
  logoArea.classList.remove("left", "center", "right");

  const align = (branding.logoAlignment || "left").toLowerCase();
  logoArea.classList.add(["left", "center", "right"].includes(align) ? align : "left");

  const wrapper = document.createElement("div");
  wrapper.style.display = "flex";

  if (align === "center") {
    wrapper.style.flexDirection = "column";
  } else if (align === "right") {
    wrapper.style.flexDirection = "row-reverse"; 
  } else {
    wrapper.style.flexDirection = "row";
  }

  wrapper.style.alignItems = "center";
  wrapper.style.gap = "5px";


  if (branding.logo) {
    const img = document.createElement("img");
    img.src = branding.logo;
    img.alt = branding.companyName || "Logo";
    img.className = "branding-logo";
    img.onerror = () => img.classList.add("hidden");
    wrapper.appendChild(img);
  }

  if (branding.companyName) {
    const nameDiv = document.createElement("div");
    nameDiv.innerText = branding.companyName;
    nameDiv.classList.add("company-name");

    if (branding.headerFontColor) nameDiv.style.color = branding.headerFontColor;
    if (branding.headerFontFamily) nameDiv.style.fontFamily = branding.headerFontFamily;
    if (branding.headerFontSize) {
      const sizeMap = { small: "14px", medium: "16px", large: "20px" };
      const sz = String(branding.headerFontSize).toLowerCase();
      nameDiv.style.fontSize = sizeMap[sz] || branding.headerFontSize;
    }
    if (branding.headerFontStyle) {
      const styleLower = String(branding.headerFontStyle).toLowerCase();
      if (styleLower.includes("italic")) nameDiv.style.fontStyle = "italic";
      if (styleLower.includes("bold")) nameDiv.style.fontWeight = "bold";
      if (styleLower.includes("normal")) {
        nameDiv.style.fontStyle = "normal";
        nameDiv.style.fontWeight = "400";
      }
    }

    if (branding.companySubtitle) {
      const subEl = document.createElement("div");
      subEl.className = "company-subtitle";
      subEl.innerText = branding.companySubtitle;
      if (branding.subtitleFontSize) subEl.style.fontSize = branding.subtitleFontSize;
      if (branding.subtitleFontColor) subEl.style.color = branding.subtitleFontColor;
      nameDiv.appendChild(subEl);
    }

    wrapper.appendChild(nameDiv);
  }

  logoArea.appendChild(wrapper);

  const langWrapper = document.getElementById("language-wrapper");
  const langSelect = document.getElementById("langSelect");
  if (showLanguageDropdown && data.languages?.length >= 1) {
    langWrapper.style.display = "block";
    langSelect.innerHTML = "";
    data.languages.forEach(lang => {
      const opt = document.createElement("option");
      opt.value = lang.toLowerCase();
      opt.text = lang;
      if (opt.value === selectedLang) opt.selected = true;
      langSelect.appendChild(opt);
    });
langSelect.onchange = async () => {
  const newLang = langSelect.value;

  setFormDisabled(true);   // instead of clearing DOM

  await fetchConsentData(newLang);

  setFormDisabled(false);
};
 } else {
    langWrapper.style.display = "none";
  }

  if (!permissions.length) {
    root.innerHTML = "<p>No consent items found.</p>";
    return;
  }
  permissions.forEach(perm => {
    const block = document.createElement("div");
    block.className = "permission-block";

    const tr = perm.permissionTranslation?.find(pt => pt.language.toLowerCase() === selectedLang);
    const htmlString = (tr?.text || perm.text || "").trim();

    const tempDiv = document.createElement("div");
    tempDiv.innerHTML = htmlString;

    const children = Array.from(tempDiv.children);

      if (children.length > 0) {
        children.forEach((child, index) => {
          const el = document.createElement(child.tagName.toLowerCase());
          el.innerHTML = child.innerHTML;

          if (child.getAttribute("style")) {
            el.setAttribute("style", child.getAttribute("style"));
          }

          if (
            /^h[1-6]$/i.test(child.tagName) &&
            !/font-weight/i.test(child.getAttribute("style") || "")
          ) {
            el.style.fontWeight = "normal";
          }

          el.style.display = "block";
          el.style.lineHeight = "1";

          // Preserve paragraph spacing and explicit blank lines from editor content.
          if (child.tagName.toLowerCase() === "p") {
            const normalized = (child.innerHTML || "").replace(/&nbsp;/g, "").trim().toLowerCase();
            const childText = (child.textContent || "").trim();
            const isBlankParagraph =
              !childText &&
              (normalized === "" || normalized === "<br>" || normalized === "<br/>" || normalized === "<br />");

            el.style.margin = "0 0 5px 0";
            el.style.minHeight = "1em";
            if (isBlankParagraph) {
              el.innerHTML = "&nbsp;";
            }
          } else {
            el.style.margin = "2px 0";
          }

          el.setAttribute("data-translate-text", perm.id);

          if (perm.mandatory && index === children.length - 1) {
                el.innerHTML += ' <span class="mandatory">*</span>';
          }

          block.appendChild(el);
        });
      } else {
        const p = document.createElement("p");
        p.textContent = htmlString.replace(/<[^>]*>/g, "");
        p.style.whiteSpace = "pre-wrap";
        p.style.margin = "0 0 5px 0";
        p.style.lineHeight = "1";
        p.setAttribute("data-translate-text", perm.id);

        if (perm.mandatory) {
          p.innerHTML += ' <span class="mandatory">*</span>';
        }

        block.appendChild(p);
      }

      const optionMap = perm.optionsMap || {};
      const options = tr?.options || perm.options || [];
      const hasOptionMap = Object.keys(optionMap).length > 0;

      if (perm.elementType === 'CHECKBOX' && enableCheckboxes) {
        if (hasOptionMap) {
            const mapEntries = Object.entries(optionMap);
            const translatedOptions = tr?.options || [];

            mapEntries.forEach(([id, baseLabel], index) => {

              const label = translatedOptions[index] || baseLabel;

              const labelEl = document.createElement("label");
              const input = document.createElement("input");

              input.type = "checkbox";
              input.name = perm.id;
              input.value = baseLabel;
              input.setAttribute("data-option-id", id);

              labelEl.appendChild(input);
              labelEl.append(" " + label);

              block.appendChild(labelEl);
            });
        } else {
          options.forEach((opt, idx) => {
            const labelEl = document.createElement("label");
            const input = document.createElement("input");
            input.type = "checkbox";
            input.name = perm.id;
            input.value = opt;
            input.setAttribute("data-option-id", idx.toString());
            labelEl.appendChild(input);
            labelEl.append(" " + opt);
            block.appendChild(labelEl);
          });
        }
      }

      if (perm.elementType === 'RADIOBUTTON' && enableRadioButtons) {
        if (hasOptionMap) {
            const mapEntries = Object.entries(optionMap);
            const translatedOptions = tr?.options || [];

            mapEntries.forEach(([id, baseLabel], index) => {

              const label = translatedOptions[index] || baseLabel;

              const labelEl = document.createElement("label");
              const input = document.createElement("input");

              input.type = "radio";
              input.name = perm.id;
              input.value = baseLabel;
              input.setAttribute("data-option-id", id);

              labelEl.appendChild(input);
              labelEl.append(" " + label);

              block.appendChild(labelEl);
            });
        } else {
          options.forEach((opt, idx) => {
            const labelEl = document.createElement("label");
            const input = document.createElement("input");
            input.type = "radio";
            input.name = perm.id;
            input.value = opt;
            input.setAttribute("data-option-id", idx.toString());
            labelEl.appendChild(input);
            labelEl.append(" " + opt);
            block.appendChild(labelEl);
          });
        }
      }


      if (perm.elementType === 'DROPDOWN' && enableDropdowns) {
        const optionEntries = hasOptionMap
          ? Object.entries(optionMap).map(([id, baseLabel], index) => ({
              id,
              baseLabel,
              label: (tr?.options || [])[index] || baseLabel
            }))
          : options.map((opt, idx) => ({ id: idx.toString(), baseLabel: opt, label: opt }));

        if (perm.allowMultipleSelection) {
          const msDropdown = document.createElement("div");
          msDropdown.className = "ms-dropdown";
          msDropdown.setAttribute("data-perm-id", perm.id);

          const control = document.createElement("div");
          control.className = "ms-control";
          control.tabIndex = 0;

          const chips = document.createElement("div");
          chips.className = "ms-chips";

          const placeholder = document.createElement("span");
          placeholder.className = "ms-placeholder";
          placeholder.textContent = "Select Options";

          const arrow = document.createElement("span");
          arrow.className = "ms-arrow";
          arrow.textContent = "▾";

          const clearAll = document.createElement("span");
          clearAll.className = "ms-clear-all";
          clearAll.textContent = "✕";
          clearAll.title = "Clear all";
          clearAll.addEventListener("click", (e) => {
            e.stopPropagation();
            panel.querySelectorAll('input[type="checkbox"]:checked').forEach(cb => {
              cb.checked = false;
              cb.closest(".ms-option")?.classList.remove("ms-option-selected");
            });
            refreshChips();
            onSelectionChange(selectedLang);
          });

          control.appendChild(chips);
          control.appendChild(placeholder);
          control.appendChild(clearAll);
          control.appendChild(arrow);

          const panel = document.createElement("div");
          panel.className = "ms-panel";
          panel.style.display = "none";

          const refreshChips = () => {
            chips.innerHTML = "";
            const checkedBoxes = panel.querySelectorAll('input[type="checkbox"]:checked');
            checkedBoxes.forEach(cb => {
              const chip = document.createElement("span");
              chip.className = "ms-chip";

              const label = document.createElement("span");
              label.textContent = cb.getAttribute("data-label") || cb.value;
              chip.appendChild(label);

              const remove = document.createElement("span");
              remove.className = "ms-chip-remove";
              remove.textContent = "✕";
              remove.addEventListener("click", (e) => {
                e.stopPropagation();
                cb.checked = false;
                refreshChips();
                onSelectionChange(selectedLang);
              });
              chip.appendChild(remove);

              chips.appendChild(chip);
            });
            placeholder.style.display = checkedBoxes.length ? "none" : "inline";
            control.classList.toggle("has-selection", checkedBoxes.length > 0);
          };

          optionEntries.forEach(entry => {
            const optionLabel = document.createElement("label");
            optionLabel.className = "ms-option";

            const checkbox = document.createElement("input");
            checkbox.type = "checkbox";
            checkbox.value = entry.baseLabel;
            checkbox.setAttribute("data-option-id", entry.id);
            checkbox.setAttribute("data-label", entry.label);

            checkbox.addEventListener("change", () => {
              optionLabel.classList.toggle("ms-option-selected", checkbox.checked);
              refreshChips();
              // Close panel after selection (mirror single-select behaviour)
              panel.style.display = "none";
              control.classList.remove("open");
              // onSelectionChange handled once by the generic block binding
            });

            optionLabel.appendChild(checkbox);
            optionLabel.append(" " + entry.label);
            panel.appendChild(optionLabel);
          });

          control.addEventListener("click", (e) => {
            e.stopPropagation();
            const isOpen = panel.style.display === "block";
            document.querySelectorAll(".ms-panel").forEach(p => p.style.display = "none");
            document.querySelectorAll(".ms-control").forEach(c => c.classList.remove("open"));
            panel.style.display = isOpen ? "none" : "block";
            control.classList.toggle("open", !isOpen);
          });

          msDropdown.appendChild(control);
          msDropdown.appendChild(panel);
          refreshChips();
          block.appendChild(msDropdown);
        } else {
          // Single-select custom dropdown (shares multiselect panel styling)
          const ssDropdown = document.createElement("div");
          ssDropdown.className = "ms-dropdown";
          ssDropdown.setAttribute("data-perm-id", perm.id);

          // Hidden native select keeps existing data-collection + validation working
          const select = document.createElement("select");
          select.name = perm.id;
          select.style.display = "none";

          const defaultOption = document.createElement("option");
          defaultOption.value = "";
          defaultOption.text = "Select Option";
          defaultOption.selected = true;
          defaultOption.disabled = true;
          select.appendChild(defaultOption);

          optionEntries.forEach(entry => {
            const option = document.createElement("option");
            option.value = entry.baseLabel;
            option.text = entry.label;
            option.setAttribute("data-option-id", entry.id);
            select.appendChild(option);
          });

          const control = document.createElement("div");
          control.className = "ms-control";
          control.tabIndex = 0;

          const valueText = document.createElement("span");
          valueText.className = "ms-chips";

          const placeholder = document.createElement("span");
          placeholder.className = "ms-placeholder";
          placeholder.textContent = "Select Option";

          const arrow = document.createElement("span");
          arrow.className = "ms-arrow";
          arrow.textContent = "▾";

          control.appendChild(valueText);
          control.appendChild(placeholder);
          control.appendChild(arrow);

          const panel = document.createElement("div");
          panel.className = "ms-panel";
          panel.style.display = "none";

          optionEntries.forEach(entry => {
            const optionLabel = document.createElement("label");
            optionLabel.className = "ms-option";
            optionLabel.textContent = entry.label;

            optionLabel.addEventListener("click", (e) => {
              e.stopPropagation();
              select.value = entry.baseLabel;

              valueText.textContent = entry.label;
              placeholder.style.display = "none";

              panel.querySelectorAll(".ms-option").forEach(o => o.classList.remove("ms-option-selected"));
              optionLabel.classList.add("ms-option-selected");

              panel.style.display = "none";
              control.classList.remove("open");

              onSelectionChange(selectedLang);
            });

            panel.appendChild(optionLabel);
          });

          control.addEventListener("click", (e) => {
            e.stopPropagation();
            const isOpen = panel.style.display === "block";
            document.querySelectorAll(".ms-panel").forEach(p => p.style.display = "none");
            document.querySelectorAll(".ms-control").forEach(c => c.classList.remove("open"));
            panel.style.display = isOpen ? "none" : "block";
            control.classList.toggle("open", !isOpen);
          });

          ssDropdown.appendChild(select);
          ssDropdown.appendChild(control);
          ssDropdown.appendChild(panel);
          block.appendChild(ssDropdown);
        }
      }

      block.querySelectorAll("input, select").forEach(function(el) {
        el.addEventListener("change", function() { onSelectionChange(selectedLang); });
      });
      root.appendChild(block);
    });



  const cancelBtn = document.getElementById("cancelBtn");
  const submitBtn = document.getElementById("submitBtn");
  const selectedLanguage = selectedLang?.toLowerCase();

  const translatedBranding = branding.brandingTranslation?.find(
    b => b.language?.toLowerCase() === selectedLanguage
  );

  const submitLabel =
    translatedBranding?.primaryButtonLabel || branding.primaryButtonLabel || "Submit";
  const cancelLabel =
    translatedBranding?.secondaryButtonLabel || branding.secondaryButtonLabel || "Cancel";

  if (showButtons) {
    cancelBtn.style.display = "block";
    cancelBtn.innerText = cancelLabel;

    submitBtn.style.display = "block";
    submitBtn.innerText = submitLabel;
    submitBtn.disabled = true; // disabled until SSS verification succeeds
    if (branding.primaryButtonbgColor) submitBtn.style.backgroundColor = branding.primaryButtonbgColor;
    if (branding.primaryFontColor) submitBtn.style.color = branding.primaryFontColor;
    if (branding.primaryButtonborderColor) submitBtn.style.borderColor = branding.primaryButtonborderColor;
    if (branding.primaryFontSize) submitBtn.style.fontSize = branding.primaryFontSize;

    if (branding.secondaryButtonBgColor) cancelBtn.style.backgroundColor = branding.secondaryButtonBgColor;
    if (branding.secondaryFontColor) cancelBtn.style.color = branding.secondaryFontColor;
    if (branding.secondaryButtonBorderColor) cancelBtn.style.borderColor = branding.secondaryButtonBorderColor;
    if (branding.secondaryFontSize) cancelBtn.style.fontSize = branding.secondaryFontSize;

    const buttonGroup = document.getElementById("button-group");
    buttonGroup.classList.remove("left", "center", "right");
    const footerAlign = branding.footerAlignment || "left";
    buttonGroup.classList.add(footerAlign.toLowerCase());
  } else {
    cancelBtn.style.display = "none";
    submitBtn.style.display = "none";
  }

  submitBtn.removeEventListener("click", clickEvent);

clickEvent = async (e) => {
    if (e) {
        e.preventDefault();
    }

    document.querySelectorAll(".error-message").forEach(el => el.remove());
    document.querySelectorAll(".error-border").forEach(el => el.classList.remove("error-border"));

    let isValid = true;

    permissions.forEach(perm => {
        if (!perm.mandatory) return;

        const name = perm.id;
        let hasValue = false;

        if (perm.elementType === "CHECKBOX" || perm.elementType === "RADIOBUTTON") {
            const inputs = document.querySelectorAll(`input[name="${name}"]:checked`);
            if (inputs.length > 0) hasValue = true;
        }

        if (perm.elementType === "DROPDOWN") {
          if (perm.allowMultipleSelection) {
            const checked = document.querySelectorAll(`.ms-dropdown[data-perm-id="${name}"] input[type="checkbox"]:checked`);
            if (checked.length > 0) hasValue = true;
          } else {
            const select = document.querySelector(`select[name="${name}"]`);
            if (select && select.value) hasValue = true;
          }
        }

        if (!hasValue) {
            isValid = false;

            const block = Array.from(document.querySelectorAll(".permission-block"))
                .find(div => div.querySelector(`[data-translate-text="${name}"]`));

            if (block) {
                const error = document.createElement("div");
                error.className = "error-message";
                error.textContent = "This field is required.";
                block.appendChild(error);

                block.querySelectorAll("input, select").forEach(el =>
                    el.classList.add("error-border")
                );

                const msControl = block.querySelector(`.ms-dropdown[data-perm-id="${name}"] .ms-control`);
                if (msControl) {
                  msControl.classList.add("error-border");
                }
            }
        }
    });

    if (!isValid) {
        showToast("Please fill all mandatory fields", "error");
        return;
    }

    const finalPayload = buildFinalConsentRequest(selectedLang);
    createConsentRequestList = finalPayload.createConsentRequestDtoWrapper;

    return await sendConsent();
};

submitBtn.addEventListener("click", clickEvent);

cancelBtn.onclick = () => {
  resetWidget(false);
};

}

function decodeJwt(token) {
  const base64Url = token.split('.')[1];
  const base64 = base64Url.replace(/-/g, '+').replace(/_/g, '/');

  const jsonPayload = decodeURIComponent(
    atob(base64)
      .split('')
      .map(c => '%' + ('00' + c.charCodeAt(0).toString(16)).slice(-2))
      .join('')
  );

  return JSON.parse(jsonPayload);
}

async function submitConsent() {
  return await sendConsent();
}

function resetConsent() {
  resetWidget();
}

function getConsentState() {
  return {
    payload: createConsentRequestList,
    jwt: consentJwt,
    sss: globalSSS
  };
}

window.consentWidget = {
    submit: async () => {
        return await clickEvent();
    },

    reset: () => {
        return resetWidget();
    }
};

initSigningKey().then(fetchConsentData);
