/// <reference path='../lib/def/jison.d.ts' />

var parser : any = function(file) {

    var Jison = require('jison');
    var bnf = require('jison/bnf');

    // synchronous fetch of grammar file (this doesn't work locally due to
    // permissions on fetching from javascript, must be run in a server)
    var r = new XMLHttpRequest();
    r.open("GET", file, false); // async fetch
    r.send(null);
    if (r.status !== 200) {
        // some error HTTP code other than OK
        throw new Error('Failed to fetch grammar "' + file + '" (' + r.status + ')');
    }

    var cfg = bnf.parse(r.responseText);
    var parser = new Jison.Generator(cfg, { type: "lalr" });

    if (parser.conflicts) {
        // taken from Jison's example file
        var msg = 'Error generating parser, conflicts encountered:';
        parser.resolutions.forEach(function(res) {
            var r = res[2];
            if (!r.bydefault)
                return null;
            msg = msg + '\n' +
            // Jison's style error message
            (r.msg + "\n" + "(" + r.s + ", " + r.r + ") -> " + r.action);
        });
        throw new Error(msg);
    }

    parser = parser.createParser();

    return (function(p) {
        return function(source) {
            try {
                return p.parse(source);
            } catch (e) {
                // wraps parser exception into one that has line numbers, etc.
                throw new ErrorWrapper(
                    e.message,
                    'Parse Error',
                    // lexer.yylineno works better than just yylineno
                    // however, we must consider the whole line to be wrong
                    { line: p.lexer.yylineno, col: 0 },
                    e,
                    e.stack
                    );
            }
        };
    })(parser);
};

// FIXME: this behaves differently from the compiled jison grammar.
// debug compiled code to see what object is returned.

// generates parser
// worker will have to consider src/ root.
parser = parser((((typeof window) === 'undefined') ? '../src/' : 'src/') + 'parser.jison');
