var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {
    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
};
var __generator = (this && this.__generator) || function (thisArg, body) {
    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g;
    return g = { next: verb(0), "throw": verb(1), "return": verb(2) }, typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;
    function verb(n) { return function (v) { return step([n, v]); }; }
    function step(op) {
        if (f) throw new TypeError("Generator is already executing.");
        while (_) try {
            if (f = 1, y && (t = op[0] & 2 ? y["return"] : op[0] ? y["throw"] || ((t = y["return"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;
            if (y = 0, t) op = [op[0] & 2, t.value];
            switch (op[0]) {
                case 0: case 1: t = op; break;
                case 4: _.label++; return { value: op[1], done: false };
                case 5: _.label++; y = op[1]; op = [0]; continue;
                case 7: op = _.ops.pop(); _.trys.pop(); continue;
                default:
                    if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }
                    if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }
                    if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }
                    if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }
                    if (t[2]) _.ops.pop();
                    _.trys.pop(); continue;
            }
            op = body.call(thisArg, _);
        } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }
        if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };
    }
};
import * as hljs from "./highlight-effekt";
import * as docs from "./docs";
function enableEditing(code, run, typecheck) {
    return __awaiter(this, void 0, void 0, function () {
        var parent, IDE, editor, module, filename, contents, prelude, postlude, model, output;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0:
                    parent = code.parentNode;
                    parent.classList.add("editor-loading");
                    return [4 /*yield*/, import(/* webpackMode: "lazy", webpackChunkName: "ide" */ "./ide")];
                case 1:
                    IDE = _a.sent();
                    return [4 /*yield*/, import(/* webpackMode: "lazy", webpackChunkName: "editor" */ "./editor")];
                case 2:
                    editor = _a.sent();
                    parent.classList.remove("editor-loading");
                    parent.classList.add("editor");
                    module = code.attributes["module"].value;
                    filename = module + ".effekt";
                    contents = code.attributes["content"].value;
                    code.textContent = "";
                    prelude = code.attributes["prelude"].value || "";
                    postlude = code.attributes["postlude"].value || "\n";
                    model = IDE.createModel(filename, contents, prelude, postlude, !!run);
                    IDE.updateModel(model);
                    model.onDidChangeContent(function (e) { IDE.updateModel(model); });
                    if (run) {
                        output = document.createElement("ul");
                        output.classList.add("repl-output");
                        parent.insertAdjacentElement("afterend", output);
                    }
                    // init editor
                    editor.create(code, typecheck, run, output, model);
                    return [2 /*return*/];
            }
        });
    });
}
function processCode() {
    var fences = document.querySelectorAll("pre > code");
    var id = 0;
    var prelude = "";
    function addMetadata(code, opts) {
        var moduleName = "module" + id++;
        code.setAttribute("module", moduleName);
        var moduleDecl = "module " + moduleName + "\n";
        var parent = code.parentElement;
        // do not add repls to prelude
        if (opts.repl) {
            parent.classList.add("repl");
            code.setAttribute("prelude", moduleDecl + prelude + "\ndef main() { println(\n");
            code.setAttribute("content", code.textContent);
            code.setAttribute("postlude", "\n) }\n");
        }
        else {
            var pre = moduleDecl + prelude;
            var post = "\n";
            code.setAttribute("prelude", pre);
            code.setAttribute("postlude", post);
            code.setAttribute("content", code.textContent);
            if (!opts.ignore) {
                prelude = prelude + "import " + moduleName + "\n";
            }
        }
    }
    function addNavigation(code, opts) {
        var nav = document.createElement("nav");
        nav.classList.add("code-menu");
        if (opts.repl) {
            var run_1 = document.createElement("a");
            run_1.setAttribute("href", "#");
            run_1.classList.add("button-run");
            run_1.textContent = "run";
            nav.append(run_1);
            run_1.onclick = function () {
                enableEditing(code, run_1, null);
                return false;
            };
        }
        else if (!opts.readOnly) {
            var edit_1 = document.createElement("a");
            edit_1.setAttribute("href", "#");
            edit_1.classList.add("button-edit");
            edit_1.textContent = "typecheck and edit";
            nav.append(edit_1);
            var activateEditor = function () {
                edit_1.onclick = function () { return false; };
                edit_1.textContent = "typecheck";
                enableEditing(code, null, edit_1);
                return false;
            };
            edit_1.onclick = activateEditor;
        }
        code.parentNode.prepend(nav);
    }
    fences.forEach(function (code) {
        var opts = classToOptions(code);
        if (opts.reset) {
            prelude = "";
        }
        if (opts.hidden) {
            code.classList.add('hidden');
            code.parentElement.classList.add('hidden');
        }
        if (opts.language != "effekt")
            return;
        if (opts.repl) {
            code.classList.add('repl');
        }
        if (opts.prelude) {
            prelude = prelude + code.textContent;
        }
        // only apply syntax highlighting
        if (opts.prelude || opts.sketch) {
            // nothing right now. Maybe add a class to indicate its prelude / sketch
        }
        else if (opts.readOnly) {
            addMetadata(code, opts);
        }
        else {
            // it should be an editor.
            addMetadata(code, opts);
            addNavigation(code, opts);
        }
        hljs.highlightBlock(code);
    });
}
var defaultLang = "effekt";
var defaultOpts = {
    language: defaultLang,
    hidden: false,
    prelude: false,
    repl: false,
    readOnly: false,
    reset: false,
    ignore: false,
    sketch: false
};
function classToOptions(dom) {
    var opts = defaultOpts;
    dom.classList.forEach(function (cls) {
        if (startsWith(cls, "language-")) {
            opts = parseOptions(cls);
        }
    });
    return opts;
}
function startsWith(s, prefix) {
    return s.indexOf(prefix) == 0;
}
function parseOptions(str) {
    var langRx = /^language-([a-zA-Z_\-$]+)/;
    var flags = str.split(':');
    var lang = langRx.exec(str)[1];
    function has(flag) { return flags.indexOf(flag) != -1; }
    return {
        language: lang,
        hidden: has("hide"),
        prelude: has("prelude"),
        repl: has("repl"),
        readOnly: has("read-only"),
        reset: has("reset"),
        ignore: has("ignore"),
        sketch: has("sketch")
    };
}
window.addEventListener("DOMContentLoaded", function () {
    processCode();
    // let codes = document.querySelectorAll("code")
    // monacoEditor(codes[codes.length - 1])
    hljs.configure({
        languages: ['effekt', 'bash']
    });
    // highlight inline code
    document.querySelectorAll("code").forEach(function (code) {
        // it is a block code
        if (code.parentElement.tagName == "pre")
            return;
        hljs.highlightBlock(code);
    });
    docs.init();
});
//# sourceMappingURL=index.js.map