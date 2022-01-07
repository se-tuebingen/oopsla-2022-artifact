var coqdocjs = coqdocjs || {};

// mini library
function $(arg) {
  if (typeof arg === 'string') {
    return toArray(document.querySelectorAll(arg));
  } else {
    return toArray(arg)
  }
}

function toArray(nl){
  return Array.prototype.slice.call(nl);
}

(function(){

function buildRegex() {
  const replacements = coqdocjs.repl;
  var keys = []
  for (var key in replacements) {
    if (replacements.hasOwnProperty(key)) {
      keys.push(key)
    }
  }
  const rx = keys.join("|")
  console.log(rx)
}

buildRegex()


const replacement = coqdocjs.repl;

function replace(s) {

  var m;
  // do something with ticks
  if (m = s.match(/^(.+)'/)) {
    return replace(m[1])+"'";
  // split into index and number and replace with index
  } else if (m = s.match(/^([A-Za-z]+)_?(\d+)$/)) {
    return replace(m[1])+m[2].replace(/\d/g, function(d){
      if (coqdocjs.subscr.hasOwnProperty(d)) {
        return coqdocjs.subscr[d];
      } else {
        return d;
      }
    });
  } else if (replacement.hasOwnProperty(s)){
    return replacement[s]
  } else {
    return s;
  }
}



function replInTextNodes() {
  $(".code > *, .inlinecode > *").forEach(node => {
    coqdocjs.replInText.forEach(toReplace => {
      // only replace if it is a text node
      if (node.nodeType != Node.TEXT_NODE) return;

      var fragments = node.textContent.split(toReplace);
      node.textContent = fragments[fragments.length-1];
      for (var k = 0; k < fragments.length - 1; ++k) {
        const parent = node.parentNode;
        parent.insertBefore(document.createTextNode(fragments[k]),node);
        const replacement = document.createElement("span");
        replacement.appendChild(document.createTextNode(toReplace));
        replacement.setAttribute("class", "id");
        replacement.setAttribute("type", "keyword");
        parent.insertBefore(replacement, node);
      }
    });
  });
}

function replNodes() {
  $(".id[type=var], .id[type=variable], .id[type=keyword], .id[type=notation], .id[type=definition], .id[type=inductive]").forEach(function(node){
    var text = node.textContent;
    var replText = replace(text);
    if(text != replText) {
      node.textContent = replText;
      node.setAttribute("title", text);
    }
  });
}

// disabled for now.
var proofs = (function() {

  function isVernacStart(l, t){
    t = t.trim();
    for(var s of l){
      if (t == s || t.startsWith(s+" ") || t.startsWith(s+".")){
        return true;
      }
    }
    return false;
  }

  function isProofStart(n){
      return isVernacStart(["Proof"], n.textContent) ||
          (isVernacStart(["Next"], n.textContent) && isVernacStart(["Obligation"], n.nextSibling.nextSibling.textContent));
  }

  function isProofEnd(s){
    return isVernacStart(["Qed", "Admitted", "Defined", "Abort"], s);
  }

  function proofStatus(){
    var proofs = $(".proof");
    if(proofs.length) {
      for(var proof of proofs) {
        if (proof.getAttribute("show") === "false") {
            return "some-hidden";
        }
      }
      return "all-shown";
    }
    else {
      return "no-proofs";
    }
  }

  function updateView(){
    document.getElementById("toggle-proofs").setAttribute("proof-status", proofStatus());
  }

  function foldProofs() {
    var hasCommands = true;
    var nodes = $(".command");
    if(nodes.length == 0) {
      hasCommands = false;
      console.log("no command tags found")
      nodes = $(".id");
    }
    nodes.forEach(function(node){
      if(isProofStart(node)) {
        var proof = document.createElement("span");
        proof.setAttribute("class", "proof");

        node.parentNode.insertBefore(proof, node);
        if(proof.previousSibling.nodeType === Node.TEXT_NODE)
          proof.appendChild(proof.previousSibling);
        while(node && !isProofEnd(node.textContent)) {
          proof.appendChild(node);
          node = proof.nextSibling;
        }
        if (proof.nextSibling) proof.appendChild(proof.nextSibling); // the Qed
        if (!hasCommands && proof.nextSibling) proof.appendChild(proof.nextSibling); // the dot after the Qed

        proof.addEventListener("click", function(proof){return function(e){
          if (e.target.parentNode.tagName.toLowerCase() === "a")
            return;
          proof.setAttribute("show", proof.getAttribute("show") === "true" ? "false" : "true");
          proof.setAttribute("animate", "");
          updateView();
        };}(proof));
        proof.setAttribute("show", "false");
      }
    });
  }

  function toggleProofs(){
    var someProofsHidden = proofStatus() === "some-hidden";
    $(".proof").forEach(function(proof){
      proof.setAttribute("show", someProofsHidden);
      proof.setAttribute("animate", "");
    });
    updateView();
  }

  return function() {
    foldProofs();
    document.getElementById("toggle-proofs").addEventListener("click", toggleProofs);
    updateView();
  }
})();

function repairDom(){
  // pull whitespace out of command
  $(".command").forEach(function(node){
    while(node.firstChild && node.firstChild.textContent.trim() == "") {
      node.parentNode.insertBefore(node.firstChild, node);
    }
  });

  // copy title attribute to type
  $(".id").forEach(node => node.setAttribute("type", node.getAttribute("title")));

  // remove links of local variables
  $("a.idref > span[type*=var]").forEach(span => span.parentNode.removeAttribute("href"));
}

function postprocess(){
  repairDom();
  // replInTextNodes()
  replNodes();

  // proofs()
}

document.addEventListener('DOMContentLoaded', postprocess);

//coqdocjs.toggleProofs = toggleProofs;
})();
