!function(e){function n(n){for(var t,a,o=n[0],i=n[1],l=0,c=[];l<o.length;l++)a=o[l],Object.prototype.hasOwnProperty.call(r,a)&&r[a]&&c.push(r[a][0]),r[a]=0;for(t in i)Object.prototype.hasOwnProperty.call(i,t)&&(e[t]=i[t]);for(s&&s(n);c.length;)c.shift()()}var t={},r={app:0};function a(n){if(t[n])return t[n].exports;var r=t[n]={i:n,l:!1,exports:{}};return e[n].call(r.exports,r,r.exports,a),r.l=!0,r.exports}a.e=function(e){var n=[],t=r[e];if(0!==t)if(t)n.push(t[2]);else{var o=new Promise((function(n,a){t=r[e]=[n,a]}));n.push(t[2]=o);var i,l=document.createElement("script");l.charset="utf-8",l.timeout=120,a.nc&&l.setAttribute("nonce",a.nc),l.src=function(e){return a.p+""+({"vendors~editor~ide":"vendors~editor~ide",ide:"ide","vendors~editor":"vendors~editor",editor:"editor"}[e]||e)+".chunk.js"}(e);var s=new Error;i=function(n){l.onerror=l.onload=null,clearTimeout(c);var t=r[e];if(0!==t){if(t){var a=n&&("load"===n.type?"missing":n.type),o=n&&n.target&&n.target.src;s.message="Loading chunk "+e+" failed.\n("+a+": "+o+")",s.name="ChunkLoadError",s.type=a,s.request=o,t[1](s)}r[e]=void 0}};var c=setTimeout((function(){i({type:"timeout",target:l})}),12e4);l.onerror=l.onload=i,document.head.appendChild(l)}return Promise.all(n)},a.m=e,a.c=t,a.d=function(e,n,t){a.o(e,n)||Object.defineProperty(e,n,{enumerable:!0,get:t})},a.r=function(e){"undefined"!=typeof Symbol&&Symbol.toStringTag&&Object.defineProperty(e,Symbol.toStringTag,{value:"Module"}),Object.defineProperty(e,"__esModule",{value:!0})},a.t=function(e,n){if(1&n&&(e=a(e)),8&n)return e;if(4&n&&"object"==typeof e&&e&&e.__esModule)return e;var t=Object.create(null);if(a.r(t),Object.defineProperty(t,"default",{enumerable:!0,value:e}),2&n&&"string"!=typeof e)for(var r in e)a.d(t,r,function(n){return e[n]}.bind(null,r));return t},a.n=function(e){var n=e&&e.__esModule?function(){return e.default}:function(){return e};return a.d(n,"a",n),n},a.o=function(e,n){return Object.prototype.hasOwnProperty.call(e,n)},a.p="/dist/",a.oe=function(e){throw console.error(e),e};var o=self.webpackJsonp=self.webpackJsonp||[],i=o.push.bind(o);o.push=n,o=o.slice();for(var l=0;l<o.length;l++)n(o[l]);var s=i;a(a.s="./src/index.ts")}({"./src/highlight-effekt.js":
/*!*********************************!*\
  !*** ./src/highlight-effekt.js ***!
  \*********************************/
/*! no static exports found */
/*! ModuleConcatenation bailout: Module is not an ECMAScript module */function(module,exports){eval("/*\nORIGINAL\n=========\nhttps://github.com/highlightjs/highlight.js/blob/master/src/languages/scala.js\n=========\nLanguage: Scala\nCategory: functional\nAuthor: Jan Berkel <jan.berkel@gmail.com>\nContributors: Erik Osheim <d_m@plastic-idolatry.com>\nWebsite: https://www.scala-lang.org\n*/\nhljs.registerLanguage(\"effekt\", function highlightEffekt(hljs) {\n\n  var ANNOTATION = { className: 'meta', begin: '@[A-Za-z]+' };\n\n  // used in strings for escaping/interpolation/substitution\n  var SUBST = {\n    className: 'subst',\n    variants: [\n      {begin: '\\\\$[A-Za-z0-9_]+'},\n      {begin: '\\\\${', end: '}'}\n    ]\n  };\n\n  var STRING = {\n    className: 'string',\n    variants: [\n      {\n        begin: '\"', end: '\"',\n        illegal: '\\\\n',\n        contains: [hljs.BACKSLASH_ESCAPE]\n      },\n      {\n        begin: '\"\"\"', end: '\"\"\"',\n        relevance: 10\n      },\n      {\n        begin: '[a-z]+\"', end: '\"',\n        illegal: '\\\\n',\n        contains: [hljs.BACKSLASH_ESCAPE, SUBST]\n      },\n      {\n        className: 'string',\n        begin: '[a-z]+\"\"\"', end: '\"\"\"',\n        contains: [SUBST],\n        relevance: 10\n      }\n    ]\n\n  };\n\n  var SYMBOL = {\n    className: 'symbol',\n    begin: '\\'\\\\w[\\\\w\\\\d_]*(?!\\')'\n  };\n\n  var TYPE = {\n    className: 'type',\n    begin: '\\\\b[A-Z][A-Za-z0-9_]*',\n    relevance: 0\n  };\n\n  var NAME = {\n    className: 'title',\n    begin: /[^0-9\\n\\t \"'(),.`{}\\[\\]:;][^\\n\\t \"'(),.`{}\\[\\]:;]+|[^0-9\\n\\t \"'(),.`{}\\[\\]:;=]/,\n    relevance: 0\n  };\n\n  var CLASS = {\n    className: 'class',\n    beginKeywords: 'class object trait type',\n    end: /[:={\\[\\n;]/,\n    excludeEnd: true,\n    contains: [\n      {\n        beginKeywords: 'extends with',\n        relevance: 10\n      },\n      {\n        begin: /\\[/,\n        end: /\\]/,\n        excludeBegin: true,\n        excludeEnd: true,\n        relevance: 0,\n        contains: [TYPE]\n      },\n      {\n        className: 'params',\n        begin: /\\(/,\n        end: /\\)/,\n        excludeBegin: true,\n        excludeEnd: true,\n        relevance: 0,\n        contains: [TYPE]\n      },\n      NAME\n    ]\n  };\n\n  var METHOD = {\n    className: 'function',\n    beginKeywords: 'def',\n    end: /[:={\\[(\\n;]/,\n    excludeEnd: true,\n    contains: [NAME]\n  };\n\n  return {\n    name: 'Scala',\n    keywords: {\n      literal: 'true false null',\n      keyword: 'return interface module type def with val var if for while import return else case try match resume box unbox at in this region'\n    },\n    contains: [\n      hljs.C_LINE_COMMENT_MODE,\n      hljs.C_BLOCK_COMMENT_MODE,\n      STRING,\n      SYMBOL,\n      TYPE,\n      METHOD,\n      CLASS,\n      hljs.C_NUMBER_MODE,\n      ANNOTATION\n    ]\n  };\n})\n\nmodule.exports = hljs\n\n\n//# sourceURL=webpack:///./src/highlight-effekt.js?")},"./src/index.ts":
/*!**********************************!*\
  !*** ./src/index.ts + 1 modules ***!
  \**********************************/
/*! no exports provided */
/*! ModuleConcatenation bailout: Cannot concat with ./src/highlight-effekt.js (<- Module is not an ECMAScript module) */function(module,__webpack_exports__,__webpack_require__){"use strict";eval('// ESM COMPAT FLAG\n__webpack_require__.r(__webpack_exports__);\n\n// EXTERNAL MODULE: ./src/highlight-effekt.js\nvar highlight_effekt = __webpack_require__("./src/highlight-effekt.js");\n\n// CONCATENATED MODULE: ./src/docs.js\n/**\n * Toggle an specific class to the received DOM element.\n * @param {string}\telemSelector The query selector specifying the target element.\n * @param {string}\t[activeClass=\'active\'] The class to be applied/removed.\n */\nfunction toggleClass(elemSelector, activeClass = "active") {\n  const elem = document.querySelector(elemSelector);\n  if (elem) {\n    elem.classList.toggle(activeClass);\n  }\n}\n\n/**\n * Toggle specific classes to an array of corresponding DOM elements.\n * @param {Array<string>}\telemSelectors The query selectors specifying the target elements.\n * @param {Array<string>}\tactiveClasses The classes to be applied/removed.\n */\nfunction toggleClasses(elemSelectors, activeClasses) {\n  elemSelectors.map((elemSelector, idx) => {\n    toggleClass(elemSelector, activeClasses[idx]);\n  });\n}\n\n/**\n * Remove active class from siblings DOM elements and apply it to event target.\n * @param {Element}\t\telement The element receiving the class, and whose siblings will lose it.\n * @param {string}\t\t[activeClass=\'active\'] The class to be applied.\n */\nfunction activate(element, activeClass = "active") {\n  [...element.parentNode.children].map(elem =>\n    elem.classList.remove(activeClass)\n  );\n  element.classList.add(activeClass);\n}\n\n/**\n * Remove active class from siblings parent DOM elements and apply it to element target parent.\n * @param {Element}\t\telement The element receiving the class, and whose siblings will lose it.\n * @param {string}\t\t[activeClass=\'active\'] The class to be applied.\n */\nfunction activateParent(element, activeClass = "active") {\n  const elemParent = element.parentNode;\n  activate(elemParent, activeClass);\n}\n\n/**\n * Remove active class from siblings parent DOM elements and apply it to element target parent.\n * @param {Element}\t\telement The element receiving the class, and whose siblings will lose it.\n * @param {string}\t\t[activeClass=\'active\'] The class to be applied.\n */\nfunction toggleParent(element, activeClass = "active") {\n  const elemParent = element.parentNode;\n  if (elemParent) {\n    elemParent.classList.toggle(activeClass);\n  }\n}\n\n/**\n * This will make the specified elements click event to show/hide the menu sidebar.\n */\nfunction activateToggle() {\n  const menuToggles = document.querySelectorAll("#menu-toggle, #main-toggle");\n  if (menuToggles) {\n    [...menuToggles].map(elem => {\n      elem.onclick = e => {\n        e.preventDefault();\n        toggleClass("#wrapper", "toggled");\n      };\n    });\n  }\n}\n\n/**\n * This will make the specified elements click event to behave as a menu\n * parent entry, or a link, or sometimes both, depending on the context.\n */\nfunction activateMenuNesting() {\n  const menuParents = document.querySelectorAll(".drop-nested");\n  if (menuParents) {\n    [...menuParents].map(elem => {\n      elem.onclick = e => {\n        e.preventDefault();\n        toggleParent(elem, "open");\n        const elementType = e.currentTarget.tagName.toLowerCase();\n        if (elementType === "a") {\n          const linkElement = e.currentTarget;\n          const linkElementParent = linkElement.parentNode;\n          const destination = linkElement.href;\n          if (\n            destination !== window.location.href &&\n            !linkElementParent.classList.contains("active")\n          ) {\n            window.location.href = destination;\n          }\n        }\n      };\n    });\n  }\n}\n\n\n/**\n * Function to create an anchor with an specific id\n * @param {string}    id The corresponding id from which the href will be created.\n * @returns {Element} The new created anchor.\n */\nfunction anchorForId(id) {\n  const anchor = document.createElement("a");\n  anchor.className = "header-link";\n  anchor.href = `#${id}`;\n  anchor.innerHTML = \'<i class="fa fa-link"></i>\';\n  return anchor;\n}\n\n/**\n * Aux function to retrieve repository stars and watchers count info from\n * @param {string}\tlevel The specific level to select header from.\n * @param {Element}\tcontainingElement The element receiving the anchor.\n */\nfunction linkifyAnchors(level, containingElement) {\n  const headers = containingElement.getElementsByTagName(`h${level}`);\n  [...headers].map(header => {\n    if (typeof header.id !== "undefined" && header.id !== "") {\n      header.append(anchorForId(header.id));\n    }\n  });\n}\n\n/**\n * Function\n */\nfunction linkifyAllLevels() {\n  const content = document.querySelector("#content");\n  [...Array(7).keys()].map(level => {\n    linkifyAnchors(level, content);\n  });\n}\n\nfunction init() {\n  if (document.body.classList.contains(\'docs\')) {\n    activateToggle();\n    activateMenuNesting();\n    linkifyAllLevels();\n  }\n}\n// CONCATENATED MODULE: ./src/index.ts\nvar __awaiter = (undefined && undefined.__awaiter) || function (thisArg, _arguments, P, generator) {\n    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }\n    return new (P || (P = Promise))(function (resolve, reject) {\n        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }\n        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }\n        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }\n        step((generator = generator.apply(thisArg, _arguments || [])).next());\n    });\n};\nvar __generator = (undefined && undefined.__generator) || function (thisArg, body) {\n    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g;\n    return g = { next: verb(0), "throw": verb(1), "return": verb(2) }, typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;\n    function verb(n) { return function (v) { return step([n, v]); }; }\n    function step(op) {\n        if (f) throw new TypeError("Generator is already executing.");\n        while (_) try {\n            if (f = 1, y && (t = op[0] & 2 ? y["return"] : op[0] ? y["throw"] || ((t = y["return"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;\n            if (y = 0, t) op = [op[0] & 2, t.value];\n            switch (op[0]) {\n                case 0: case 1: t = op; break;\n                case 4: _.label++; return { value: op[1], done: false };\n                case 5: _.label++; y = op[1]; op = [0]; continue;\n                case 7: op = _.ops.pop(); _.trys.pop(); continue;\n                default:\n                    if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }\n                    if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }\n                    if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }\n                    if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }\n                    if (t[2]) _.ops.pop();\n                    _.trys.pop(); continue;\n            }\n            op = body.call(thisArg, _);\n        } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }\n        if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };\n    }\n};\n\n\nfunction enableEditing(code, run, typecheck) {\n    return __awaiter(this, void 0, void 0, function () {\n        var parent, IDE, editor, module, filename, contents, prelude, postlude, model, output;\n        return __generator(this, function (_a) {\n            switch (_a.label) {\n                case 0:\n                    parent = code.parentNode;\n                    parent.classList.add("editor-loading");\n                    return [4 /*yield*/, Promise.all(/*! import() | ide */[__webpack_require__.e("vendors~editor~ide"), __webpack_require__.e("ide")]).then(__webpack_require__.bind(null, /*! ./ide */ "./src/ide.ts"))];\n                case 1:\n                    IDE = _a.sent();\n                    return [4 /*yield*/, Promise.all(/*! import() | editor */[__webpack_require__.e("vendors~editor~ide"), __webpack_require__.e("vendors~editor"), __webpack_require__.e("ide"), __webpack_require__.e("editor")]).then(__webpack_require__.bind(null, /*! ./editor */ "./src/editor.ts"))];\n                case 2:\n                    editor = _a.sent();\n                    parent.classList.remove("editor-loading");\n                    parent.classList.add("editor");\n                    module = code.attributes["module"].value;\n                    filename = module + ".effekt";\n                    contents = code.attributes["content"].value;\n                    code.textContent = "";\n                    prelude = code.attributes["prelude"].value || "";\n                    postlude = code.attributes["postlude"].value || "\\n";\n                    model = IDE.createModel(filename, contents, prelude, postlude, !!run);\n                    IDE.updateModel(model);\n                    model.onDidChangeContent(function (e) { IDE.updateModel(model); });\n                    if (run) {\n                        output = document.createElement("ul");\n                        output.classList.add("repl-output");\n                        parent.insertAdjacentElement("afterend", output);\n                    }\n                    // init editor\n                    editor.create(code, typecheck, run, output, model);\n                    return [2 /*return*/];\n            }\n        });\n    });\n}\nfunction processCode() {\n    var fences = document.querySelectorAll("pre > code");\n    var id = 0;\n    var prelude = "";\n    function addMetadata(code, opts) {\n        var moduleName = "module" + id++;\n        code.setAttribute("module", moduleName);\n        var moduleDecl = "module " + moduleName + "\\n";\n        var parent = code.parentElement;\n        // do not add repls to prelude\n        if (opts.repl) {\n            parent.classList.add("repl");\n            code.setAttribute("prelude", moduleDecl + prelude + "\\ndef main() { println(\\n");\n            code.setAttribute("content", code.textContent);\n            code.setAttribute("postlude", "\\n) }\\n");\n        }\n        else {\n            var pre = moduleDecl + prelude;\n            var post = "\\n";\n            code.setAttribute("prelude", pre);\n            code.setAttribute("postlude", post);\n            code.setAttribute("content", code.textContent);\n            if (!opts.ignore) {\n                prelude = prelude + "import " + moduleName + "\\n";\n            }\n        }\n    }\n    function addNavigation(code, opts) {\n        var nav = document.createElement("nav");\n        nav.classList.add("code-menu");\n        if (opts.repl) {\n            var run_1 = document.createElement("a");\n            run_1.setAttribute("href", "#");\n            run_1.classList.add("button-run");\n            run_1.textContent = "run";\n            nav.append(run_1);\n            run_1.onclick = function () {\n                enableEditing(code, run_1, null);\n                return false;\n            };\n        }\n        else if (!opts.readOnly) {\n            var edit_1 = document.createElement("a");\n            edit_1.setAttribute("href", "#");\n            edit_1.classList.add("button-edit");\n            edit_1.textContent = "typecheck and edit";\n            nav.append(edit_1);\n            var activateEditor = function () {\n                edit_1.onclick = function () { return false; };\n                edit_1.textContent = "typecheck";\n                enableEditing(code, null, edit_1);\n                return false;\n            };\n            edit_1.onclick = activateEditor;\n        }\n        code.parentNode.prepend(nav);\n    }\n    fences.forEach(function (code) {\n        var opts = classToOptions(code);\n        if (opts.reset) {\n            prelude = "";\n        }\n        if (opts.hidden) {\n            code.classList.add(\'hidden\');\n            code.parentElement.classList.add(\'hidden\');\n        }\n        if (opts.language != "effekt")\n            return;\n        if (opts.repl) {\n            code.classList.add(\'repl\');\n        }\n        if (opts.prelude) {\n            prelude = prelude + code.textContent;\n        }\n        // only apply syntax highlighting\n        if (opts.prelude || opts.sketch) {\n            // nothing right now. Maybe add a class to indicate its prelude / sketch\n        }\n        else if (opts.readOnly) {\n            addMetadata(code, opts);\n        }\n        else {\n            // it should be an editor.\n            addMetadata(code, opts);\n            addNavigation(code, opts);\n        }\n        highlight_effekt["highlightBlock"](code);\n    });\n}\nvar defaultLang = "effekt";\nvar defaultOpts = {\n    language: defaultLang,\n    hidden: false,\n    prelude: false,\n    repl: false,\n    readOnly: false,\n    reset: false,\n    ignore: false,\n    sketch: false\n};\nfunction classToOptions(dom) {\n    var opts = defaultOpts;\n    dom.classList.forEach(function (cls) {\n        if (startsWith(cls, "language-")) {\n            opts = parseOptions(cls);\n        }\n    });\n    return opts;\n}\nfunction startsWith(s, prefix) {\n    return s.indexOf(prefix) == 0;\n}\nfunction parseOptions(str) {\n    var langRx = /^language-([a-zA-Z_\\-$]+)/;\n    var flags = str.split(\':\');\n    var lang = langRx.exec(str)[1];\n    function has(flag) { return flags.indexOf(flag) != -1; }\n    return {\n        language: lang,\n        hidden: has("hide"),\n        prelude: has("prelude"),\n        repl: has("repl"),\n        readOnly: has("read-only"),\n        reset: has("reset"),\n        ignore: has("ignore"),\n        sketch: has("sketch")\n    };\n}\nwindow.addEventListener("DOMContentLoaded", function () {\n    processCode();\n    // let codes = document.querySelectorAll("code")\n    // monacoEditor(codes[codes.length - 1])\n    highlight_effekt["configure"]({\n        languages: [\'effekt\', \'bash\']\n    });\n    // highlight inline code\n    document.querySelectorAll("code").forEach(function (code) {\n        // it is a block code\n        if (code.parentElement.tagName == "pre")\n            return;\n        highlight_effekt["highlightBlock"](code);\n    });\n    init();\n});\n\n\n//# sourceURL=webpack:///./src/index.ts_+_1_modules?')}});