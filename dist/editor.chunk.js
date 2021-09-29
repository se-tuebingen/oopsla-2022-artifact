(self.webpackJsonp=self.webpackJsonp||[]).push([["editor"],{"./src/editor.ts":
/*!***********************************!*\
  !*** ./src/editor.ts + 1 modules ***!
  \***********************************/
/*! exports provided: create */
/*! ModuleConcatenation bailout: Cannot concat with ./node_modules/monaco-editor/esm/vs/editor/browser/controller/coreCommands.js */
/*! ModuleConcatenation bailout: Cannot concat with ./node_modules/monaco-editor/esm/vs/editor/contrib/hover/hover.js */
/*! ModuleConcatenation bailout: Cannot concat with ./node_modules/monaco-editor/esm/vs/editor/contrib/wordHighlighter/wordHighlighter.js */
/*! ModuleConcatenation bailout: Cannot concat with ./node_modules/monaco-editor/esm/vs/editor/editor.api.js */
/*! ModuleConcatenation bailout: Cannot concat with ./src/ide.ts (<- Module is referenced from these modules with unsupported syntax: ./src/index.ts (referenced with import())) */function(module,__webpack_exports__,__webpack_require__){"use strict";eval("// ESM COMPAT FLAG\n__webpack_require__.r(__webpack_exports__);\n\n// EXPORTS\n__webpack_require__.d(__webpack_exports__, \"create\", function() { return /* binding */ create; });\n\n// EXTERNAL MODULE: ./node_modules/monaco-editor/esm/vs/editor/editor.api.js + 77 modules\nvar editor_api = __webpack_require__(\"./node_modules/monaco-editor/esm/vs/editor/editor.api.js\");\n\n// EXTERNAL MODULE: ./node_modules/monaco-editor/esm/vs/editor/browser/controller/coreCommands.js + 2 modules\nvar coreCommands = __webpack_require__(\"./node_modules/monaco-editor/esm/vs/editor/browser/controller/coreCommands.js\");\n\n// EXTERNAL MODULE: ./node_modules/monaco-editor/esm/vs/editor/contrib/hover/hover.js + 83 modules\nvar hover = __webpack_require__(\"./node_modules/monaco-editor/esm/vs/editor/contrib/hover/hover.js\");\n\n// EXTERNAL MODULE: ./node_modules/monaco-editor/esm/vs/editor/contrib/wordHighlighter/wordHighlighter.js\nvar wordHighlighter = __webpack_require__(\"./node_modules/monaco-editor/esm/vs/editor/contrib/wordHighlighter/wordHighlighter.js\");\n\n// CONCATENATED MODULE: ./src/effekt-syntax.ts\nvar syntax = {\n    // defaultToken: 'invalid',\n    keywords: [\n        'module', 'import', 'def', 'val', 'var', 'effect', 'type', 'match',\n        'case', 'record', 'extern', 'include', 'resume', 'with', 'if', 'try',\n        'else', 'do', 'handle', 'while', 'interface', 'box', 'unbox'\n    ],\n    definitionKeywords: [\n        'def', 'type', 'effect'\n    ],\n    literals: ['true', 'false'],\n    operators: [\n        '=', '>', '<', '!', '~', '?', ':', '==', '<=', '>=', '!=',\n        '&&', '||', '++', '--', '+', '-', '*', '/', '&', '|', '^', '%',\n        '<<', '>>', '>>>', '+=', '-=', '*=', '/=', '&=', '|=', '^=',\n        '%=', '<<=', '>>=', '>>>='\n    ],\n    // we include these common regular expressions\n    symbols: /[=><!~?:&|+\\-*\\/\\^%]+/,\n    // The main tokenizer for our languages\n    tokenizer: {\n        root: [\n            // identifiers and keywords\n            [/[a-z_$][\\w$]*/, {\n                    cases: {\n                        '@keywords': {\n                            cases: {\n                                '@definitionKeywords': { token: 'keyword', next: '@definition' },\n                                '@default': 'keyword'\n                            }\n                        },\n                        '@literals': 'literal',\n                        '@default': 'identifier'\n                    }\n                }],\n            [/[A-Z][\\w\\$]*/, 'type.identifier'],\n            // whitespace\n            { include: '@whitespace' },\n            // delimiters and operators\n            [/[{}()\\[\\]]/, '@brackets'],\n            [/[<>](?!@symbols)/, '@brackets'],\n            [/@symbols/, { cases: { '@operators': 'operator',\n                        '@default': '' } }],\n            // numbers\n            [/\\d*\\.\\d+([eE][\\-+]?\\d+)?/, 'number.float'],\n            [/0[xX][0-9a-fA-F]+/, 'number.hex'],\n            [/\\d+/, 'number'],\n            // delimiter: after number because of .\\d floats\n            [/[;,.]/, 'delimiter'],\n            // strings\n            [/\"([^\"\\\\]|\\\\.)*$/, 'string.invalid'],\n            [/\"/, { token: 'string.quote', bracket: '@open', next: '@string' }],\n            // characters\n            [/'[^\\\\']'/, 'string'],\n            [/'/, 'string.invalid']\n        ],\n        definition: [\n            { include: '@whitespace' },\n            [/[a-zA-Z_$][\\w$]*/, 'definition'],\n            [new RegExp(\"\"), '', '@pop']\n        ],\n        comment: [\n            [/[^\\/*]+/, 'comment']\n        ],\n        string: [\n            [/[^\\\\\"]+/, 'string'],\n            [/\\\\./, 'string.escape.invalid'],\n            [/\"/, { token: 'string.quote', bracket: '@close', next: '@pop' }]\n        ],\n        whitespace: [\n            [/[ \\t\\r\\n]+/, 'white'],\n            [/\\/\\*/, 'comment', '@comment'],\n            [/\\/\\/.*$/, 'comment'],\n        ],\n    },\n};\nvar docsTheme = {\n    base: 'vs',\n    inherit: false,\n    colors: {\n        \"editor.background\": \"#f8f8f7\"\n    },\n    rules: [\n        { token: '', foreground: '333333', background: 'f8f8f7' },\n        { token: 'keyword', foreground: '333333', fontStyle: 'bold' },\n        { token: 'identifier', foreground: '333333' },\n        { token: 'type.identifier', foreground: 'd73a49' },\n        { token: 'definition', foreground: '735080' },\n        { token: 'custom-info', foreground: '808080' },\n        { token: 'string', foreground: '25995f' },\n        { token: 'number', foreground: '005cc5' },\n        { token: 'comment', foreground: '969896' },\n        { token: 'literal', foreground: '0086b3' }\n    ]\n};\nvar pageTheme = {\n    base: 'vs',\n    inherit: false,\n    colors: {\n        \"editor.background\": \"#ffffff\"\n    },\n    rules: [\n        { token: '', foreground: '333333', background: 'f8f8f7' },\n        { token: 'keyword', foreground: '333333', fontStyle: 'bold' },\n        { token: 'identifier', foreground: '333333' },\n        { token: 'type.identifier', foreground: 'd73a49' },\n        { token: 'definition', foreground: '735080' },\n        { token: 'custom-info', foreground: '808080' },\n        { token: 'string', foreground: '25995f' },\n        { token: 'number', foreground: '005cc5' },\n        { token: 'comment', foreground: '969896' },\n        { token: 'literal', foreground: '0086b3' }\n    ]\n};\n\n// EXTERNAL MODULE: ./src/ide.ts\nvar ide = __webpack_require__(\"./src/ide.ts\");\n\n// CONCATENATED MODULE: ./src/editor.ts\n// import * as monaco from \"monaco-editor\";\n\n\n\n\n\n\n//@ts-ignore\nself.MonacoEnvironment = {\n    getWorkerUrl: function (moduleId, label) {\n        return \"/dist/editor.worker.bundle.js\";\n    }\n};\neditor_api[\"languages\"].register({ id: 'effekt' });\neditor_api[\"languages\"].setMonarchTokensProvider('effekt', syntax);\neditor_api[\"editor\"].defineTheme('effekt-docs-theme', docsTheme);\neditor_api[\"editor\"].defineTheme('effekt-page-theme', pageTheme);\n// TODO hover provider with XHR here:\n//   https://github.com/microsoft/monaco-editor/blob/master/test/playground.generated/extending-language-services-hover-provider-example.html\neditor_api[\"languages\"].registerHoverProvider('effekt', ide[\"hoverProvider\"]);\nfunction create(container, run, out, model) {\n    var theme = document.body.classList.contains(\"docs\") ? \"effekt-docs-theme\" : \"effekt-page-theme\";\n    var editor = editor_api[\"editor\"].create(container, {\n        // contents\n        model: model,\n        // set language and theme\n        language: \"effekt\",\n        theme: theme,\n        fontSize: 13,\n        fontFamily: \"'Fira Mono', monospace\",\n        // minimal mode: disable most features\n        minimap: { enabled: false },\n        lineNumbers: \"off\",\n        automaticLayout: false,\n        scrollBeyondLastLine: false,\n        folding: false,\n        contextmenu: false,\n        matchBrackets: \"never\",\n        overviewRulerBorder: false,\n        cursorStyle: \"line\",\n        renderFinalNewline: false,\n        renderLineHighlight: \"none\",\n        fixedOverflowWidgets: true,\n        lightbulb: {\n            enabled: false\n        },\n        quickSuggestions: false,\n        scrollbar: {\n            handleMouseWheel: false,\n            alwaysConsumeMouseWheel: false,\n            horizontal: \"hidden\",\n            useShadows: false,\n            vertical: \"hidden\"\n        }\n    });\n    // autoBlur(editor)\n    autoResize(editor);\n    registerTypechecking(editor);\n    // type check once for hover\n    ide[\"typecheck\"](model);\n    addRunAction(editor, run, out);\n    return editor;\n}\nfunction autoBlur(editor) {\n    // remove classes current-line on blur\n    editor.onDidBlurEditorText(function () {\n        editor.getDomNode().querySelectorAll(\".current-line\").forEach(function (n) {\n            return n.classList.remove(\"current-line\");\n        });\n    });\n}\nfunction autoResize(editor) {\n    editor.onDidChangeModelContent(function () {\n        updateEditorHeight(); // typing\n        // requestAnimationFrame(updateEditorHeight) // folding\n    });\n    var prevHeight = 0;\n    function updateEditorHeight() {\n        var editorElement = editor.getDomNode();\n        if (!editorElement) {\n            return;\n        }\n        var widthPx = editorElement.style.width;\n        var width = Math.max(parseInt(widthPx.substr(0, widthPx.length - 2)), editor.getContentWidth());\n        var height = editor.getContentHeight();\n        if (prevHeight !== height) {\n            editor.layout({\n                width: width,\n                height: height\n            });\n        }\n    }\n    updateEditorHeight();\n}\nfunction registerTypechecking(editor) {\n    var timeout;\n    editor.onDidChangeModelContent(function (evt) {\n        if (timeout) {\n            clearTimeout(timeout);\n        }\n        var model = editor.getModel();\n        timeout = setTimeout(function () { return ide[\"typecheck\"](model); }, 150);\n    });\n}\nfunction addRunAction(editor, run, output) {\n    function evaluate(editor) {\n        var log = console.log;\n        // TODO this does not work with async or setTimeout, find another solution!\n        output.innerHTML = \"\";\n        // delay evaluation to get the impression we are actually doing something\n        window.setTimeout(function () {\n            try {\n                console.log = function (msg) {\n                    var logLine = document.createElement(\"li\");\n                    logLine.innerText = msg;\n                    output.appendChild(logLine);\n                };\n                ide[\"evaluate\"](editor.getModel().getFullText());\n                output.classList.remove(\"cleared\");\n            }\n            catch (e) {\n                console.log(e);\n            }\n            finally {\n                console.log = log;\n                output.classList.remove(\"cleared\");\n            }\n        }, 150);\n        return false;\n    }\n    if (run) {\n        run.onclick = function () { return evaluate(editor); };\n        editor.addAction({\n            id: 'effekt-run',\n            label: 'Run code',\n            keybindings: [editor_api[\"KeyCode\"].Enter],\n            precondition: null,\n            keybindingContext: null,\n            contextMenuGroupId: 'navigation',\n            contextMenuOrder: 1.5,\n            run: evaluate\n        });\n        // eval once after adding editor support\n        evaluate(editor);\n    }\n}\n\n\n//# sourceURL=webpack:///./src/editor.ts_+_1_modules?")}}]);