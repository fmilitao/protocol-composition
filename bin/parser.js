/// <reference path='../lib/def/jison.d.ts' />
var parser = function (file) {
    var Jison = require('jison');
    var bnf = require('jison/bnf');
    var r = new XMLHttpRequest();
    r.open("GET", file, false);
    r.send(null);
    if (r.status !== 200) {
        throw new Error('Failed to fetch grammar "' + file + '" (' + r.status + ')');
    }
    var cfg = bnf.parse(r.responseText);
    var parser = new Jison.Generator(cfg, { type: "lalr" });
    if (parser.conflicts) {
        var msg = 'Error generating parser, conflicts encountered:';
        parser.resolutions.forEach(function (res) {
            var r = res[2];
            if (!r.bydefault)
                return null;
            msg = msg + '\n' +
                (r.msg + "\n" + "(" + r.s + ", " + r.r + ") -> " + r.action);
        });
        throw new Error(msg);
    }
    parser = parser.createParser();
    return (function (p) {
        return function (source) {
            try {
                return p.parse(source);
            }
            catch (e) {
                throw new ErrorWrapper(e.message, 'Parse Error', { line: p.lexer.yylineno, col: 0 }, e, e.stack);
            }
        };
    })(parser);
};
parser = parser(((typeof (window) === 'undefined') ? '../src/' : 'src/') + 'parser.jison');
