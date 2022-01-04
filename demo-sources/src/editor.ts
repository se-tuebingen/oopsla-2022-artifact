// import * as monaco from "monaco-editor";
import * as monaco from "monaco-editor/esm/vs/editor/editor.api";
import "monaco-editor/esm/vs/editor/browser/controller/coreCommands";
import "monaco-editor/esm/vs/editor/contrib/hover/hover";
import "monaco-editor/esm/vs/editor/contrib/wordHighlighter/wordHighlighter";
import { syntax, docsTheme, pageTheme } from "./effekt-syntax";
import * as IDE from "./ide"

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


export function create(container: HTMLElement, typecheck: HTMLElement, run: HTMLElement, out: HTMLElement, model: IDE.IViewModel): monaco.editor.ICodeEditor {

  let theme = document.body.classList.contains("docs") ? "effekt-docs-theme" : "effekt-page-theme";

  let editor = monaco.editor.create(container, {
    // contents
    model: model,

    // set language and theme
    language: "effekt",
    theme: theme,
    fontSize: 13,
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
  autoResize(editor)

  // type check once for hover
  IDE.typecheck(model)
  IDE.annotateCaptures(model)

  addRunAction(editor, run, out)
  addTypecheckAction(editor, typecheck)
  registerErrorDetection(editor, container)

  return editor;
}

function autoBlur(editor: monaco.editor.ICodeEditor) {
  // remove classes current-line on blur
  editor.onDidBlurEditorText(function() {
    editor.getDomNode().querySelectorAll(".current-line").forEach(n =>
      n.classList.remove("current-line")
    )
  });
}

function autoResize(editor: monaco.editor.ICodeEditor) {
  editor.onDidChangeModelContent(() => {
    updateEditorHeight() // typing
    // requestAnimationFrame(updateEditorHeight) // folding
  })

  var prevHeight = 0
  function updateEditorHeight() {
    const editorElement = editor.getDomNode()
    if (!editorElement) { return }
    let widthPx = editorElement.style.width
    let width = Math.max(parseInt(widthPx.substr(0, widthPx.length - 2)), editor.getContentWidth())
    let height = editor.getContentHeight()

    if (prevHeight !== height) {
      editor.layout({
        width: width,
        height: height
      })
    }
  }
  updateEditorHeight();
}


function registerErrorDetection(editor: monaco.editor.ICodeEditor, dom: HTMLElement) {
  let model = editor.getModel() as IDE.IViewModel
  editor.onDidChangeModelDecorations(() => {
    let diagnostics = monaco.editor.getModelMarkers({ owner: "effekt", resource: model.uri });
    if (diagnostics.filter(d => d.severity >= monaco.MarkerSeverity.Error).length > 0) {
      dom.classList.add("hasError");
    } else {
      dom.classList.remove("hasError");
    }
  });
}

function addRunAction(editor, run, output) {
  function evaluate(editor) {
    const log = console.log
    let model = editor.getModel();

    IDE.typecheck(model);

    // TODO this does not work with async or setTimeout, find another solution!
    output.innerHTML = ""

    try {
      console.log = function(msg) {
        const logLine = document.createElement("li");
        logLine.innerText = msg
        output.appendChild(logLine)
      }
      IDE.evaluate(model.getFullText())
      output.classList.remove("cleared")
    } catch (e) {
      console.log(e)
    } finally {
      console.log = log
      output.classList.remove("cleared")
    }

    return false;
  }

  if (run) {
    run.onclick = () => evaluate(editor)

    editor.addAction({
      id: 'effekt-run',
      label: 'Run code',
      keybindings: [ monaco.KeyCode.Enter ],
      precondition: null,
      keybindingContext: null,
      contextMenuGroupId: 'navigation',
      contextMenuOrder: 1.5,
      run: evaluate
    });

    // eval once after adding editor support
    evaluate(editor)
  }
}

function addTypecheckAction(editor, typecheckButton) {
  function typecheck(editor) {
    let model = editor.getModel();
    IDE.typecheck(model);
    IDE.annotateCaptures(model);
    return false;
  }

  if (typecheckButton) {
    typecheckButton.onclick = () => typecheck(editor)

    editor.addAction({
      id: 'effekt-typecheck',
      label: 'Typecheck code',
      keybindings: [ monaco.KeyMod.CtrlCmd | monaco.KeyCode.Enter ],
      precondition: null,
      keybindingContext: null,
      contextMenuGroupId: 'navigation',
      contextMenuOrder: 1.5,
      run: typecheck
    });

    // check once after adding editor support
    typecheck(editor)
  }
}