/**
 * The (conceptual) webworker.
 *
 * Right now, we are not implementing it as a webworker, but with a synchronous API.
 * The API also is using vscode-types since the Effekt language server implements LSP
 */
import { effekt } from "./effekt";
var Effekt = effekt.LanguageServer();
export function inferredCaptures(filename) {
    return Effekt.inferredCaptures(filename);
}
export function typecheck(filename) {
    return Effekt.typecheck(filename);
}
export function write(filename, content) {
    Effekt.writeFile(filename, content);
}
export function infoAt(filename, position) {
    return Effekt.infoAt(filename, position);
}
export function definitionAt(filename, position) {
    return Effekt.definitionAt(filename, position);
}
export function load(path) {
    var console = { log: self.console.log };
    var require = load;
    var module = { exports: null };
    var compiled = Effekt.compileFile(path);
    // console.log(compiled)
    eval("(function() { " + compiled + "}).apply(this)");
    return module.exports;
}
export function evaluate(content) {
    var console = { log: self.console.log };
    var require = load;
    var module = { exports: null };
    var compiled = Effekt.compileString(content);
    // console.log(compiled)
    eval("(function() { " + compiled + "}).apply(this)");
    var result = module.exports.main().run();
    return result;
}
//# sourceMappingURL=effekt-language.js.map