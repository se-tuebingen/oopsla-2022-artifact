// import * as monaco from "monaco-editor";
import * as monaco from "monaco-editor/esm/vs/editor/editor.api";
import "monaco-editor/esm/vs/editor/browser/controller/coreCommands";
import "monaco-editor/esm/vs/editor/contrib/hover/hover";
import "monaco-editor/esm/vs/editor/contrib/wordHighlighter/wordHighlighter";
import { syntax, docsTheme, pageTheme } from "./effekt-syntax";
import * as IDE from "./ide";
//@ts-ignore
self.MonacoEnvironment = {
    getWorkerUrl: function (moduleId, label) {
        return "/dist/editor.worker.bundle.js";
    }
};
monaco.languages.register({ id: 'effekt' });
monaco.languages.setMonarchTokensProvider('effekt', syntax);
monaco.editor.defineTheme('effekt-docs-theme', docsTheme);
monaco.editor.defineTheme('effekt-page-theme', pageTheme);
// TODO hover provider with XHR here:
//   https://github.com/microsoft/monaco-editor/blob/master/test/playground.generated/extending-language-services-hover-provider-example.html
monaco.languages.registerHoverProvider('effekt', IDE.hoverProvider);
monaco.languages.registerDefinitionProvider('effekt', IDE.definitionProvider);
export function create(container, typecheck, run, out, model) {
    var theme = document.body.classList.contains("docs") ? "effekt-docs-theme" : "effekt-page-theme";
    var editor = monaco.editor.create(container, {
        // contents
        model: model,
        // set language and theme
        language: "effekt",
        theme: theme,
        fontSize: 14,
        fontFamily: "'Fira Mono', monospace",
        // minimal mode: disable most features
        minimap: { enabled: false },
        lineNumbers: "off",
        automaticLayout: false,
        scrollBeyondLastLine: false,
        folding: false,
        contextmenu: false,
        matchBrackets: "never",
        overviewRulerBorder: false,
        cursorStyle: "line",
        renderFinalNewline: false,
        renderLineHighlight: "none",
        fixedOverflowWidgets: true,
        lightbulb: {
            enabled: false
        },
        quickSuggestions: false,
        scrollbar: {
            handleMouseWheel: false,
            alwaysConsumeMouseWheel: false,
            horizontal: "hidden",
            useShadows: false,
            vertical: "hidden"
        }
    });
    // autoBlur(editor)
    autoResize(editor);
    // type check once for hover
    IDE.typecheck(model);
    IDE.annotateCaptures(model);
    addRunAction(editor, run, out);
    addTypecheckAction(editor, typecheck);
    registerErrorDetection(editor, container);
    return editor;
}
function autoBlur(editor) {
    // remove classes current-line on blur
    editor.onDidBlurEditorText(function () {
        editor.getDomNode().querySelectorAll(".current-line").forEach(function (n) {
            return n.classList.remove("current-line");
        });
    });
}
function autoResize(editor) {
    editor.onDidChangeModelContent(function () {
        updateEditorHeight(); // typing
        // requestAnimationFrame(updateEditorHeight) // folding
    });
    var prevHeight = 0;
    function updateEditorHeight() {
        var editorElement = editor.getDomNode();
        if (!editorElement) {
            return;
        }
        var widthPx = editorElement.style.width;
        var width = Math.max(parseInt(widthPx.substr(0, widthPx.length - 2)), editor.getContentWidth());
        var height = editor.getContentHeight();
        if (prevHeight !== height) {
            editor.layout({
                width: width,
                height: height
            });
        }
    }
    updateEditorHeight();
}
function registerErrorDetection(editor, dom) {
    var model = editor.getModel();
    editor.onDidChangeModelDecorations(function () {
        var diagnostics = monaco.editor.getModelMarkers({ owner: "effekt", resource: model.uri });
        if (diagnostics.filter(function (d) { return d.severity >= monaco.MarkerSeverity.Error; }).length > 0) {
            dom.classList.add("hasError");
        }
        else {
            dom.classList.remove("hasError");
        }
    });
}
function addRunAction(editor, run, output) {
    function evaluate(editor) {
        var log = console.log;
        var model = editor.getModel();
        IDE.typecheck(model);
        // TODO this does not work with async or setTimeout, find another solution!
        output.innerHTML = "";
        try {
            console.log = function (msg) {
                var logLine = document.createElement("li");
                logLine.innerText = msg;
                output.appendChild(logLine);
            };
            IDE.evaluate(model.getFullText());
            output.classList.remove("cleared");
        }
        catch (e) {
            console.log(e);
        }
        finally {
            console.log = log;
            output.classList.remove("cleared");
        }
        return false;
    }
    if (run) {
        run.onclick = function () { return evaluate(editor); };
        editor.addAction({
            id: 'effekt-run',
            label: 'Run code',
            keybindings: [monaco.KeyCode.Enter],
            precondition: null,
            keybindingContext: null,
            contextMenuGroupId: 'navigation',
            contextMenuOrder: 1.5,
            run: evaluate
        });
        // eval once after adding editor support
        evaluate(editor);
    }
}
function addTypecheckAction(editor, typecheckButton) {
    function typecheck(editor) {
        var model = editor.getModel();
        IDE.typecheck(model);
        IDE.annotateCaptures(model);
        return false;
    }
    if (typecheckButton) {
        typecheckButton.onclick = function () { return typecheck(editor); };
        editor.addAction({
            id: 'effekt-typecheck',
            label: 'Typecheck code',
            keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.Enter],
            precondition: null,
            keybindingContext: null,
            contextMenuGroupId: 'navigation',
            contextMenuOrder: 1.5,
            run: typecheck
        });
        // check once after adding editor support
        typecheck(editor);
    }
}
//# sourceMappingURL=editor.js.map