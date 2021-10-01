/**
 * The (conceptual) webworker.
 *
 * The API is using vscode-types since the Effekt language server implements LSP
 */
import * as effekt from "./effekt-language";
import * as monaco from "monaco-editor/esm/vs/editor/editor.api";
import type { Diagnostic, DiagnosticSeverity, Position, Location } from "vscode-languageserver-types"

// initialize:
// load all code[module=...] elements and write them to the IDE
document.querySelectorAll("code[module]").forEach( (code: HTMLElement) => {
  let module = code.getAttribute("module")
  let filename = module + ".effekt"
  let content = code.getAttribute("prelude") + code.getAttribute("content") + code.getAttribute("postlude")
  effekt.write(filename, content)
})

export interface IViewModel extends monaco.editor.ITextModel {
  getFullText(): string
  modelPosition(pos: Position): Position
  viewPosition(pos: Position): Position
  modelLocation(loc: Location): Location
  viewLocation(loc: Location): Location
  showCaptures(): Boolean
}

export function createModel(filename: string, contents: string, hiddenPrelude: string, hiddenPostlude: string, isRepl: Boolean): IViewModel {
  let model = monaco.editor.createModel(contents.trim(), "effekt", monaco.Uri.file(filename))
  let pre = hiddenPrelude || ""
  let post = hiddenPostlude || ""
  let lineOffset = (hiddenPrelude.match(/\n/g) || '').length

  function modelPosition(viewPos: Position): Position {
    viewPos = viewPos || { line: 0, character: 0 }
    return { line: (viewPos.line || 0) + lineOffset, character: viewPos.character || 0 }
  }
  function viewPosition(modelPos: Position): Position {
    modelPos = modelPos || { line: 0, character: 0 }
    return { line: (modelPos.line || 0) - lineOffset, character: modelPos.character || 0 }
  }
  function modelLocation(viewLoc: Location): Location {
    const from = viewLoc.range.start
    const to = viewLoc.range.end
    return { uri: viewLoc.uri, range: { start: modelPosition(from), end: modelPosition(to) } }
  }
  function viewLocation(modelLoc: Location): Location {
    const from = modelLoc.range.start
    const to = modelLoc.range.end
    return { uri: modelLoc.uri, range: { start: viewPosition(from), end: viewPosition(to) } }
  }

  //@ts-ignore
  model.getFullText = function() {
    return pre + model.getValue() + post
  }
  //@ts-ignore
  model.modelPosition = modelPosition
  //@ts-ignore
  model.viewPosition = viewPosition
  //@ts-ignore
  model.modelLocation = modelLocation
  //@ts-ignore
  model.viewLocation = viewLocation

  //@ts-ignore
  model.showCaptures = function() { return !isRepl }

  //@ts-ignore
  return model
}

export function annotateCaptures(model: IViewModel) {

  if (!model.showCaptures()) return;

  let captures = effekt.inferredCaptures(filename(model.uri));

  let decorations = captures.map(c => {
    let p = toMonacoPosition(model.viewPosition(c.pos))
    let d: monaco.editor.IModelDeltaDecoration = {
      range: new monaco.Range(p.lineNumber, p.column, p.lineNumber, p.column),
      options: {
        before: {
          content: c.capture,
          inlineClassName: "captureset",
          inlineClassNameAffectsLetterSpacing: true
        }
      }
    }
    return d
  })
  // we could implement something more efficient here...
  let old = model.getAllDecorations().map(d => d.id)
  model.deltaDecorations(old, decorations)

}

export function typecheck(model: IViewModel) {
  updateModel(model)
  var diagnostics = effekt.typecheck(filename(model.uri)).map( (d: Diagnostic) => {
    d.range.start = model.viewPosition(d.range.start)
    d.range.end = model.viewPosition(d.range.end)
    return convertDiagnostics(d)
  })

  monaco.editor.setModelMarkers(model, "effekt", diagnostics);
}

export function updateModel(model: IViewModel) {
  writeFile(filename(model.uri), model.getFullText())
}

export function writeFile(path: string, content: string) {
  effekt.write(path, content)
}

export function evaluate(content: string) {
  return effekt.evaluate(content)
}

export const hoverProvider: monaco.languages.HoverProvider = {
  provideHover: function(model, position, token) {
    const m = model as IViewModel
    const info: string = effekt.infoAt(filename(model.uri), m.modelPosition(toLspPosition(position)))
    if (info) {
      return { contents: [{ value: info }] }
    } else {
      return null
    }
  }
}

export const definitionProvider: monaco.languages.DefinitionProvider = {
  provideDefinition: function(model, position, token) {
    const m = model as IViewModel
    const loc = effekt.definitionAt(filename(model.uri), m.modelPosition(toLspPosition(position)))
    // TODO convert from LSP location to view location
    return toMonacoLocation(m.viewLocation(loc))
  }
}

// extracts the path and drops the leading /
function filename(uri: monaco.Uri): string {
  return uri.path.substring(1)
}


// Monaco vs LSP

function convertDiagnostics(d: Diagnostic): monaco.editor.IMarkerData {
  return {
    startLineNumber: (d.range.start.line || 0) + 1,
    startColumn: (d.range.start.character || 0) + 1,
    endLineNumber: (d.range.end.line || 0) + 1,
    endColumn: (d.range.end.character || 0) + 1,
    severity: convertSeverity(d.severity),
    message: d.message
  };
}

function toMonacoPosition(position: Position): monaco.Position {
  return new monaco.Position(position.line + 1, position.character + 1)
}

function toLspPosition(position: monaco.Position): Position {
  return { line: position.lineNumber - 1, character: position.column - 1 }
}

function toMonacoLocation(loc: Location): monaco.languages.Location {
  const from = toMonacoPosition(loc.range.start)
  const to = toMonacoPosition(loc.range.end)
  return { uri: monaco.Uri.parse(loc.uri), range: new monaco.Range(from.lineNumber, from.column, to.lineNumber, to.column) }
}


function convertSeverity(lspSeverity: DiagnosticSeverity): monaco.MarkerSeverity {
  switch (lspSeverity) {
    case 1: return monaco.MarkerSeverity.Error
    case 2: return monaco.MarkerSeverity.Warning
    case 3: return monaco.MarkerSeverity.Info
    case 4: return monaco.MarkerSeverity.Hint
  }
}
