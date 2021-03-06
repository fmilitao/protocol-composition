// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
var isWorker = typeof (window) === 'undefined';
var IMPORTS = [
    '../lib/jison.js',
    'setup.comm.js',
    'ast.js',
    'parser.js',
    'typechecker.types.js',
    'typechecker.utils.js',
    'typechecker.composition.js',
    'typechecker.js'];
if (isWorker) {
    var console = function () {
        function aux(k, arg) {
            var tmp = [];
            for (var i = 0; i < arg.length; ++i)
                tmp.push(arg[i].toString());
            self.postMessage({ kind: k, data: '[Worker] ' + tmp.join(' ') });
        }
        ;
        return {
            log: function () { aux('log', arguments); },
            error: function () { aux('error', arguments); },
            debug: function () { aux('debug', arguments); }
        };
    }();
    importScripts.apply(null, IMPORTS);
}
var WebWorker;
(function (WebWorker) {
    var types = TypeChecker.types;
    var checker = TypeChecker.checker;
    function parse(txt) {
        try {
            return parser.parse(txt);
        }
        catch (e) {
            throw new ErrorWrapper(e.message, 'Parse Error', { line: parser.lexer.yylineno, col: 0 }, e, e.stack);
        }
    }
    ;
    var send = Comm.WorkerThread.getRemoteEditor();
    var receiver = (function () {
        var ast = null;
        var info = null;
        function handleErrors(es) {
            send.setErrorStatus('Error' + ((es.length > 1) ? 's (' + es.length + ')' : '') + '!');
            es.forEach(function (e) { return console.error(e.stack.toString()); });
            send.errorHandler(es);
        }
        ;
        return {
            eval: function (data) {
                try {
                    ast = null;
                    info = null;
                    send.clearAll();
                    send.setStatus('Type checking...');
                    ast = parse(data);
                    var i = checker(ast);
                    var errors = i.info.filter(function (j) { return j instanceof ErrorWrapper; });
                    if (errors.length > 0) {
                        handleErrors(errors);
                        return;
                    }
                    info = i.info;
                    if (!isWorker) {
                        console.debug('Checked in ' + i.time + ' ms.');
                    }
                    send.setOKStatus('Checked in ' + i.time + ' ms.');
                    send.clearAnnotations();
                }
                catch (e) {
                    handleErrors([e]);
                }
            },
            checker: function (pos) {
                if (info === null)
                    return;
                var ptr = null;
                for (var _i = 0; _i < info.length; _i++) {
                    var _a = info[_i], ast_1 = _a[0], table = _a[1];
                    if (ast_1.line === pos.row) {
                        ptr = table;
                        break;
                    }
                }
                send.clearAll();
                if (ptr === null)
                    return;
                send.println(printComposition(ptr));
            }
        };
    })();
    Comm.WorkerThread.setLocalWorker(receiver);
    var printAST = function (ast, r) {
        var res = '';
        if (r !== undefined && r !== null) {
            if (r instanceof Array) {
                res = '\n\nComposition: ' + printComposition(r);
            }
            else {
                res = '\n\nType: ' + toHTML(r) + '\n Str: ' + r.toString(true);
            }
        }
        return "@" + (ast.line + 1) + ":" + ast.col + '-'
            + (ast.last_line + 1) + ':' + ast.last_col + ' ' + ast.kind
            + res + '\n';
    };
    function printComposition(cf) {
        var tmp = '<table class="typing_composition"><tr>' +
            '<th>#</th>' +
            '<th>State</th>' +
            '<th>P</th><th>Q</th>' +
            '</tr>';
        for (var i = 0; i < cf.length; ++i) {
            var _a = cf[i], s = _a.s, p = _a.p, q = _a.q;
            tmp += '<tr>' + '<td>' + i + '</td>' +
                '<td>' + toHTML(s) + '</td>' +
                '<td>' + toHTML(p) + '</td>' +
                '<td>' + toHTML(q) + '</td>' +
                '</tr>';
        }
        return tmp + '</table>';
    }
    ;
    var printEnvironment = function (env) {
        var gamma = _printEnvironment(env);
        gamma = gamma.join(',\n    ');
        if (gamma === '')
            gamma = '&empty;';
        return "\u0393 = " + gamma;
    };
    var _printEnvironment = function (env) {
        var gamma = [];
        env.forEach(function (i, id, type, bound) {
            if (id === undefined || id === null)
                return;
            if (type.type === types.LocationVariable) {
                gamma.push('<span class="type_location">' + id + '<sup>' + i + '</sup></span>: <b>loc</b>');
            }
            if (type.type === types.TypeVariable) {
                gamma.push('<span class="type_variable">' + id + '<sup>' + i + '</sup></span>: <b>type</b>');
            }
            if (bound !== null && bound !== undefined) {
                gamma.push('<span class="type_variable">' + id + '<sup>' + i + '</span> <: ' + toHTML(bound));
            }
        });
        return gamma;
    };
    var info = function (tp, pos) {
        var type_info = tp.info;
        var diff = tp.diff;
        var ptr = null;
        var indexes = [];
        for (var i in type_info) {
            var ast = type_info[i].ast;
            if (ptr === null) {
                ptr = i;
                indexes = [i];
            }
            else {
                var old = type_info[ptr].ast;
                var dy = Math.abs(ast.line - pos.row);
                var _dy = Math.abs(old.line - pos.row);
                if (dy < _dy) {
                    ptr = i;
                    indexes = [i];
                    continue;
                }
                if (dy === _dy) {
                    var dx = Math.abs(ast.col - pos.column);
                    var _dx = Math.abs(old.col - pos.column);
                    if (dx < _dx) {
                        ptr = i;
                        indexes = [i];
                        continue;
                    }
                    else {
                        if (dx === _dx) {
                            indexes.push(i);
                            continue;
                        }
                    }
                }
            }
        }
        if (ptr === null || indexes.length === 0)
            return '';
        var msg = '<b title="click to hide">Type Information</b> (' + diff + 'ms)';
        var res = [];
        for (var i = 0; i < indexes.length; ++i) {
            var ptr = indexes[i];
            var as = printAST(type_info[ptr].ast, type_info[ptr].res);
            var ev = printEnvironment(type_info[ptr].env);
            var cf = type_info[ptr].composition;
            cf = (cf !== undefined ? printComposition(cf) : '');
            var seen = false;
            for (var j = 0; !seen && j < res.length; ++j) {
                var jj = res[j];
                if (jj.env === ev) {
                    jj.ast += '<br/>' + as;
                    if (jj.cf === '')
                        jj.cf += cf;
                    seen = true;
                    break;
                }
            }
            if (!seen) {
                res.push({ ast: as, env: ev, cf: cf });
            }
        }
        for (var i = 0; i < res.length; ++i) {
            var tmp = res[i];
            msg += "<hr class='type_hr'/>"
                + tmp.ast
                + '<br/>'
                + tmp.env
                + tmp.cf;
        }
        return msg;
    };
    var _toHTML = function (t) {
        if (t.type === types.ReferenceType ||
            t.type === types.FunctionType ||
            t.type === types.StackedType ||
            t.type === types.StarType ||
            t.type === types.AlternativeType ||
            t.type === types.IntersectionType ||
            t.type === types.SumType) {
            return '(' + toHTML(t) + ')';
        }
        return toHTML(t);
    };
    var wq = function (t) { return '<span class="q">' + t + '</span>'; };
    var wQ = function (t) { return '<span class="Q">' + t + '</span>'; };
    var toHTML = function (t) {
        switch (t.type) {
            case types.FunctionType:
                return wq(wq(_toHTML(t.argument())) +
                    wQ(' &#x22b8; ') +
                    wq(_toHTML(t.body())));
            case types.BangType: {
                var inner = t.inner();
                return wq(wQ("!") + wq(_toHTML(t.inner())));
            }
            case types.SumType: {
                var tags = t.tags();
                var res = [];
                for (var i in tags) {
                    res.push(wQ('<span class="type_tag">' + tags[i] + '</span>#') +
                        wq(_toHTML(t.inner(tags[i]))));
                }
                return wq(res.join('+'));
            }
            case types.StarType: {
                var inners = t.inner();
                var res = [];
                for (var i = 0; i < inners.length; ++i)
                    res.push(wq(_toHTML(inners[i])));
                return wq(res.join(wQ(' * ')));
            }
            case types.IntersectionType: {
                var inners = t.inner();
                var res = [];
                for (var i = 0; i < inners.length; ++i)
                    res.push(wq(_toHTML(inners[i])));
                return wq(res.join(wQ(' &amp; ')));
            }
            case types.AlternativeType: {
                var inners = t.inner();
                var res = [];
                for (var i = 0; i < inners.length; ++i)
                    res.push(wq(_toHTML(inners[i])));
                return wq(res.join(wQ(' &#8853; ')));
            }
            case types.ExistsType:
                return '&#8707;' +
                    (t.id().type === types.LocationVariable ?
                        '<span class="type_location">' :
                        '<span class="type_variable">')
                    + t.id().name() + '</span>'
                    + (t.bound() !== null ? '<:' + _toHTML(t.bound()) : '') + '.'
                    + _toHTML(t.inner());
            case types.ForallType:
                return '&#8704;' +
                    (t.id().type === types.LocationVariable ?
                        '<span class="type_location">' :
                        '<span class="type_variable">')
                    + t.id().name() + '</span>'
                    + (t.bound() !== null ? '<:' + _toHTML(t.bound()) : '') + '.'
                    + _toHTML(t.inner());
            case types.ReferenceType:
                return "<b>ref</b> " + toHTML(t.location());
            case types.CapabilityType:
                return '<b>rw</b> ' +
                    toHTML(t.location()) + ' ' +
                    toHTML(t.value());
            case types.StackedType:
                return wq(wq(toHTML(t.left())) + wQ(' :: ') + wq(toHTML(t.right())));
            case types.RecordType: {
                var res = [];
                var fields = t.fields();
                for (var i in fields)
                    res.push('<span class="type_field">' + i + '</span>: ' + toHTML(fields[i]));
                return "[" + res.join(', ') + "]";
            }
            case types.TupleType: {
                var res = [];
                var values = t.inner();
                for (var i in values)
                    res.push(toHTML(values[i]));
                return "[" + res.join(', ') + "]";
            }
            case types.LocationVariable:
                return '<span class="type_location">' + t.name() + '<sup>' + t.index() + '</sup></span>';
            case types.TypeVariable:
                return '<span class="type_variable">' + t.name() + '<sup>' + t.index() + '</sup></span>';
            case types.PrimitiveType:
                return '<b>' + t.name() + '</b>';
            case types.NoneType:
                return '<b>none</b>';
            case types.TopType:
                return '<b>top</b>';
            case types.RecursiveType: {
                var t_def = '<span class="type_definition">' + t.definition() + '</span>';
                if (t.args().length === 0)
                    return wq(t_def);
                var res = [];
                var as = t.args();
                for (var i in as)
                    res.push(toHTML(as[i]));
                return wq(t_def + wQ('[') + res.join(', ') + wQ(']'));
            }
            case types.RelyType:
                return wq(wq(_toHTML(t.rely())) + wQ(' &#8658; ') + wq(_toHTML(t.guarantee())));
            case types.GuaranteeType:
                return wq(wq(_toHTML(t.guarantee())) + wQ(' ; ') + wq(_toHTML(t.rely())));
            default:
                console.error("Error @toHTML: " + t.type);
                return null;
        }
    };
})(WebWorker || (WebWorker = {}));
//# sourceMappingURL=setup.worker.js.map