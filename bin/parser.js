/// <reference path='../lib/def/jison.d.ts' />
var Jison;
(function (Jison_1) {
    var GRAMMAR = ((typeof window) === 'undefined' ? '../' : '') + 'src/parser.jison';
    Jison_1.parser = GenerateParser(GRAMMAR);
    function GenerateParser(file) {
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
        return parser.createParser();
    }
    ;
})(Jison || (Jison = {}));
;
var parser = Jison.parser;
//# sourceMappingURL=parser.js.map