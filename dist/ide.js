/**
 * The (conceptual) webworker.
 *
 * The API is using vscode-types since the Effekt language server implements LSP
 */
import * as effekt from "./effekt-language";
import * as monaco from "monaco-editor/esm/vs/editor/editor.api";
// initialize:
// load all code[module=...] elements and write them to the IDE
document.querySelectorAll("code[module]").forEach(function (code) {
    var module = code.getAttribute("module");
    var filename = module + ".effekt";
    var content = code.getAttribute("prelude") + code.getAttribute("content") + code.getAttribute("postlude");
    effekt.write(filename, content);
});
export function createModel(filename, contents, hiddenPrelude, hiddenPostlude, isRepl) {
    var model = monaco.editor.createModel(contents.trim(), "effekt", monaco.Uri.file(filename));
    var pre = hiddenPrelude || "";
    var post = hiddenPostlude || "";
    var lineOffset = (hiddenPrelude.match(/\n/g) || '').length;
    function modelPosition(viewPos) {
        viewPos = viewPos || { line: 0, character: 0 };
        return { line: (viewPos.line || 0) + lineOffset, character: viewPos.character || 0 };
    }
    function viewPosition(modelPos) {
        modelPos = modelPos || { line: 0, character: 0 };
        return { line: (modelPos.line || 0) - lineOffset, character: modelPos.character || 0 };
    }
    function modelLocation(viewLoc) {
        var from = viewLoc.range.start;
        var to = viewLoc.range.end;
        return { uri: viewLoc.uri, range: { start: modelPosition(from), end: modelPosition(to) } };
    }
    function viewLocation(modelLoc) {
        var from = modelLoc.range.start;
        var to = modelLoc.range.end;
        return { uri: modelLoc.uri, range: { start: viewPosition(from), end: viewPosition(to) } };
    }
    //@ts-ignore
    model.getFullText = function () {
        return pre + model.getValue() + post;
    };
    //@ts-ignore
    model.modelPosition = modelPosition;
    //@ts-ignore
    model.viewPosition = viewPosition;
    //@ts-ignore
    model.modelLocation = modelLocation;
    //@ts-ignore
    model.viewLocation = viewLocation;
    //@ts-ignore
    model.showCaptures = function () { return !isRepl; };
    //@ts-ignore
    return model;
}
export function annotateCaptures(model) {
    if (!model.showCaptures())
        return;
    var captures = effekt.inferredCaptures(filename(model.uri));
    var decorations = captures.map(function (c) {
        var p = toMonacoPosition(model.viewPosition(c.pos));
        var d = {
            range: new monaco.Range(p.lineNumber, p.column, p.lineNumber, p.column),
            options: {
                before: {
                    content: c.capture,
                    inlineClassName: "captureset",
                    inlineClassNameAffectsLetterSpacing: true
                }
            }
        };
        return d;
    });
    // we could implement something more efficient here...
    var old = model.getAllDecorations().map(function (d) { return d.id; });
    model.deltaDecorations(old, decorations);
}
export function typecheck(model) {
    updateModel(model);
    var diagnostics = effekt.typecheck(filename(model.uri)).map(function (d) {
        d.range.start = model.viewPosition(d.range.start);
        d.range.end = model.viewPosition(d.range.end);
        return convertDiagnostics(d);
    });
    monaco.editor.setModelMarkers(model, "effekt", diagnostics);
}
export function updateModel(model) {
    writeFile(filename(model.uri), model.getFullText());
}
export function writeFile(path, content) {
    effekt.write(path, content);
}
export function evaluate(content) {
    return effekt.evaluate(content);
}
export var hoverProvider = {
    provideHover: function (model, position, token) {
        var m = model;
        var info = effekt.infoAt(filename(model.uri), m.modelPosition(toLspPosition(position)));
        if (info) {
            return { contents: [{ value: info }] };
        }
        else {
            return null;
        }
    }
};
export var definitionProvider = {
    provideDefinition: function (model, position, token) {
        var m = model;
        var loc = effekt.definitionAt(filename(model.uri), m.modelPosition(toLspPosition(position)));
        // TODO convert from LSP location to view location
        return toMonacoLocation(m.viewLocation(loc));
    }
};
// extracts the path and drops the leading /
function filename(uri) {
    return uri.path.substring(1);
}
// Monaco vs LSP
function convertDiagnostics(d) {
    return {
        startLineNumber: (d.range.start.line || 0) + 1,
        startColumn: (d.range.start.character || 0) + 1,
        endLineNumber: (d.range.end.line || 0) + 1,
        endColumn: (d.range.end.character || 0) + 1,
        severity: convertSeverity(d.severity),
        message: d.message
    };
}
function toMonacoPosition(position) {
    return new monaco.Position(position.line + 1, position.character + 1);
}
function toLspPosition(position) {
    return { line: position.lineNumber - 1, character: position.column - 1 };
}
function toMonacoLocation(loc) {
    var from = toMonacoPosition(loc.range.start);
    var to = toMonacoPosition(loc.range.end);
    return { uri: monaco.Uri.parse(loc.uri), range: new monaco.Range(from.lineNumber, from.column, to.lineNumber, to.column) };
}
function convertSeverity(lspSeverity) {
    switch (lspSeverity) {
        case 1: return monaco.MarkerSeverity.Error;
        case 2: return monaco.MarkerSeverity.Warning;
        case 3: return monaco.MarkerSeverity.Info;
        case 4: return monaco.MarkerSeverity.Hint;
    }
}
//# sourceMappingURL=ide.js.map