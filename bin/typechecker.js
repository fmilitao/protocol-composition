// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
var TypeChecker = (function (AST, exports) {
    var assert = exports.assert;
    var error = exports.error;
    var types = exports.types;
    var fct = exports.factory;
    var FunctionType = fct.FunctionType;
    var BangType = fct.BangType;
    var SumType = fct.SumType;
    var StarType = fct.StarType;
    var AlternativeType = fct.AlternativeType;
    var IntersectionType = fct.IntersectionType;
    var ForallType = fct.ForallType;
    var ExistsType = fct.ExistsType;
    var RecordType = fct.RecordType;
    var TupleType = fct.TupleType;
    var ReferenceType = fct.ReferenceType;
    var StackedType = fct.StackedType;
    var CapabilityType = fct.CapabilityType;
    var LocationVariable = fct.LocationVariable;
    var TypeVariable = fct.TypeVariable;
    var PrimitiveType = fct.PrimitiveType;
    var RelyType = fct.RelyType;
    var DefinitionType = fct.DefinitionType;
    var GuaranteeType = fct.GuaranteeType;
    var UnitType = new BangType(new RecordType());
    var NoneType = new fct.NoneType();
    var TopType = new fct.TopType();
    var Gamma = exports.Gamma;
    var TypeDefinition = exports.TypeDefinition;
    var shift = exports.shift;
    var unify = exports.unify;
    var unfold = exports.unfold;
    var unfoldDefinition = exports.unfoldDefinition;
    var substitution = exports.substitution;
    var subtype = exports.subtype;
    var equals = exports.equals;
    var isFree = exports.isFree;
    var isProtocol = exports.isProtocol;
    var indexSet = exports.indexSet;
    var isTypeVariableName = function (n) {
        return n[0] === n[0].toUpperCase();
    };
    var unifyRely = function (id, step, state) {
        switch (step.type) {
            case types.ExistsType:
                return unifyRely(shift(id, 0, 1), step.inner(), shift(state, 0, 1));
            case types.RelyType:
                return unify(id, step.rely(), state);
            case types.AlternativeType: {
                var is = step.inner();
                for (var i = 0; i < is.length; ++i) {
                    var tmp = unifyRely(id, is[i], state);
                    if (tmp !== false)
                        return tmp;
                }
                return false;
            }
            case types.IntersectionType: {
                var is = step.inner();
                var res = null;
                for (var i = 0; i < is.length; ++i) {
                    var tmp = unifyRely(id, is[i], state);
                    if (tmp === false)
                        return tmp;
                    if (res === null) {
                        res = tmp;
                    }
                    else {
                        if (!equals(res, tmp))
                            return false;
                    }
                }
                return res;
            }
            default:
                return false;
        }
    };
    var unifyGuarantee = function (id, step, state) {
        switch (step.type) {
            case types.ForallType:
                return unifyGuarantee(shift(id, 0, 1), step.inner(), shift(state, 0, 1));
            case types.GuaranteeType:
                return unify(id, step.guarantee(), state);
            case types.AlternativeType: {
                var is = step.inner();
                for (var i = 0; i < is.length; ++i) {
                    var tmp = unifyGuarantee(id, is[i], state);
                    if (tmp !== false)
                        return tmp;
                }
                return false;
            }
            case types.IntersectionType: {
                var is = step.inner();
                var res = null;
                for (var i = 0; i < is.length; ++i) {
                    var tmp = unifyGuarantee(id, is[i], state);
                    if (tmp === false)
                        return tmp;
                    if (res === null) {
                        res = tmp;
                    }
                    else {
                        if (!equals(res, tmp))
                            return false;
                    }
                }
                return res;
            }
            default:
                return false;
        }
    };
    var contains = function (visited, w) {
        for (var _i = 0; _i < visited.length; _i++) {
            var v = visited[_i];
            if (subtype(w.s, v.s) &&
                subtype(v.p, w.p) &&
                subtype(v.q, w.q))
                return true;
        }
        return false;
    };
    var Work = function (s, p, q) {
        return { s: s, p: p, q: q };
    };
    var checkConformance = function (g, s, p, q) {
        var work = [Work(s, p, q)];
        var visited = [];
        return checkConformanceAux(work, visited);
    };
    var checkConformanceAux = function (work, visited) {
        while (work.length > 0) {
            var w = work.pop();
            if (!contains(visited, w)) {
                var s = w.s;
                var p = w.p;
                var q = w.q;
                var left = step(s, p, q, true);
                var right = step(s, q, p, false);
                if (left === null || right === null)
                    return null;
                work = work.concat(left).concat(right);
                visited.push(w);
            }
        }
        return visited;
    };
    var step = function (s, p, q, isLeft) {
        s = unfold(s);
        p = unfold(p);
        var res = singleStep(s, p, q, isLeft);
        if (res !== null)
            return res;
        if (s.type === types.AlternativeType) {
            var ss = s.inner();
            var res = [];
            for (var i = 0; i < ss.length; ++i) {
                var tmp = step(ss[i], p, q, isLeft);
                if (tmp === null) {
                    res = null;
                    break;
                }
                res = res.concat(tmp);
            }
            if (res !== null)
                return res;
        }
        if (p.type === types.IntersectionType) {
            var pp = p.inner();
            var res = [];
            for (var i = 0; i < pp.length; ++i) {
                var tmp = step(s, pp[i], q, isLeft);
                if (tmp === null) {
                    res = null;
                    break;
                }
                res = res.concat(tmp);
            }
            if (res !== null)
                return res;
        }
        if (p.type === types.AlternativeType) {
            var pp = p.inner();
            for (var i = 0; i < pp.length; ++i) {
                var tmp = step(s, pp[i], q, isLeft);
                if (tmp !== null)
                    return tmp;
            }
        }
        if (s.type === types.IntersectionType) {
            var ss = s.inner();
            for (var i = 0; i < ss.length; ++i) {
                var tmp = step(ss[i], p, q, isLeft);
                if (tmp !== null)
                    return tmp;
            }
        }
        return null;
    };
    var singleStep = function (s, p, q, isLeft) {
        var R = function (s, p) {
            var tmp = reIndex(s, p, q);
            s = tmp[0];
            p = tmp[1];
            q = tmp[2];
            return isLeft ? Work(s, p, q) : Work(s, q, p);
        };
        if (p.type === types.NoneType) {
            return [];
        }
        if (isProtocol(s)) {
            if (s.type === types.ExistsType && p.type === types.ExistsType) {
                if (s.id().type !== p.id().type)
                    return null;
                return step(s.inner(), p.inner(), shift(q, 0, 1), isLeft);
            }
            if (s.type === types.RelyType && s.guarantee().type === types.ForallType &&
                p.type === types.RelyType && p.guarantee().type === types.ForallType) {
                var gs = s.guarantee();
                var gp = p.guarantee();
                if (gs.id().type !== gp.id().type)
                    return null;
                s = new RelyType(shift(s.rely(), 0, 1), gs.inner());
                p = new RelyType(shift(p.rely(), 0, 1), gs.inner());
                q = shift(q, 0, 1);
                return step(s, p, q, isLeft);
            }
            if (s.type === types.RelyType && s.guarantee().type === types.ForallType &&
                p.type === types.RelyType && p.guarantee().type !== types.ForallType) {
                var b = s.guarantee();
                var i = b.id();
                var t = b.inner();
                b = p.guarantee();
                if (b.type === types.GuaranteeType)
                    b = b.guarantee();
                var x = unifyGuarantee(i, t, shift(b, 0, 1));
                if (x === false)
                    return null;
                if (x !== true) {
                    t = substitution(t, i, x);
                }
                t = shift(t, 0, -1);
                return step(new RelyType(s.rely(), t), p, q, isLeft);
            }
            if (s.type === types.RelyType && p.type === types.RelyType && subtype(s.rely(), p.rely())) {
                var gs = s.guarantee();
                var gp = p.guarantee();
                if (gs.type !== types.GuaranteeType) {
                    gs = new GuaranteeType(gs, NoneType);
                }
                if (gp.type !== types.GuaranteeType) {
                    gp = new GuaranteeType(gp, NoneType);
                }
                if (subtype(gp.guarantee(), gs.guarantee())) {
                    return [R(gs.rely(), gp.rely())];
                }
            }
            return null;
        }
        else {
            if (equals(s, p)) {
                return [R(NoneType, NoneType)];
            }
            if (p.type === types.ExistsType) {
                var i = p.id();
                var t = p.inner();
                var x = unifyRely(i, t, shift(s, 0, 1));
                if (x === false)
                    return null;
                if (x !== true) {
                    t = substitution(t, i, x);
                }
                t = shift(t, 0, -1);
                return step(s, t, q, isLeft);
            }
            if (p.type === types.RelyType && p.guarantee().type === types.ForallType) {
                p = new RelyType(shift(p.rely(), 0, 1), p.guarantee().inner());
                q = shift(q, 0, 1);
                s = shift(s, 0, 1);
                return step(s, p, q, isLeft);
            }
            if (p.type === types.RelyType && subtype(s, p.rely())) {
                var b = p.guarantee();
                if (b.type === types.GuaranteeType) {
                    return [R(b.guarantee(), b.rely())];
                }
                else {
                    return [R(b, NoneType)];
                }
            }
            return null;
        }
    };
    var reIndex = function (s, a, b) {
        var set = indexSet(s);
        indexSet(a).forEach(function (v) { set.add(v); });
        indexSet(b).forEach(function (v) { set.add(v); });
        if (set.size > 0) {
            var v = [];
            set.forEach(function (val) { v.push(val); });
            v.sort();
            for (var i = 0; i < v.length; ++i) {
                if (v[i] !== i) {
                    v[i] = i - v[i] - (i > 0 ? v[i - 1] : 0);
                }
                else {
                    v[i] = 0;
                }
            }
            for (var i = 0; i < v.length; ++i) {
                if (v[i] < 0) {
                    s = shift(s, i, v[i]);
                    a = shift(a, i, v[i]);
                    b = shift(b, i, v[i]);
                }
            }
        }
        return [s, a, b];
    };
    var setupAST = function (kind, check) {
        switch (kind) {
            case AST.SUBSTITUTION:
                return function (ast, env) {
                    var type = check(ast.type, env);
                    var to = check(ast.to, env);
                    var from = check(ast.from, env);
                    assert((from.type === types.LocationVariable || from.type === types.TypeVariable)
                        || ("Can only substitute a Type/LocationVariable, got: " + from.type), ast.from);
                    return substitution(type, from, to);
                };
            case AST.SUBTYPE:
                return function (ast, env) {
                    var left = check(ast.a, env);
                    var right = check(ast.b, env);
                    var s = subtype(left, right);
                    assert(s == ast.value || ('Unexpected Result, got ' + s + ' expecting ' + ast.value), ast);
                    return left;
                };
            case AST.EQUALS:
                return function (ast, env) {
                    var left = check(ast.a, env);
                    var right = check(ast.b, env);
                    var s = equals(left, right);
                    assert(s == ast.value || ('Unexpected Result, got ' + s + ' expecting ' + ast.value), ast);
                    return left;
                };
            case AST.SUM_TYPE:
                return function (ast, env) {
                    var sum = new SumType();
                    for (var i = 0; i < ast.sums.length; ++i) {
                        var tag = ast.sums[i].tag;
                        assert(sum.add(tag, check(ast.sums[i].exp, env)) ||
                            "Duplicated tag: " + tag, ast.sums[i]);
                    }
                    return sum;
                };
            case AST.INTERSECTION_TYPE:
                return function (ast, env) {
                    var alt = new IntersectionType();
                    for (var i = 0; i < ast.types.length; ++i) {
                        alt.add(check(ast.types[i], env));
                    }
                    return alt;
                };
            case AST.ALTERNATIVE_TYPE:
                return function (ast, env) {
                    var alt = new AlternativeType();
                    for (var i = 0; i < ast.types.length; ++i) {
                        alt.add(check(ast.types[i], env));
                    }
                    return alt;
                };
            case AST.STAR_TYPE:
                return function (ast, env) {
                    var star = new StarType();
                    for (var i = 0; i < ast.types.length; ++i) {
                        star.add(check(ast.types[i], env));
                    }
                    return star;
                };
            case AST.NAME_TYPE:
                return function (ast, env) {
                    var label = ast.text;
                    var typedef = env.getTypeDef();
                    var tmp = env.getTypeByName(label);
                    if (tmp !== undefined &&
                        (tmp.type === types.TypeVariable ||
                            tmp.type === types.LocationVariable)) {
                        return tmp.copy(env.getNameIndex(label));
                    }
                    var lookup_args = typedef.getType(label);
                    if (lookup_args !== undefined && lookup_args.length === 0)
                        return new DefinitionType(label, [], typedef);
                    assert('Unknown type ' + label, ast);
                };
            case AST.DEFINITION_TYPE:
                return function (ast, env) {
                    var typedef = env.getTypeDef();
                    var id = ast.name;
                    var args = ast.args;
                    var t_args = typedef.getType(id);
                    assert(t_args !== undefined || ('Unknown typedef: ' + id), ast);
                    assert(t_args.length === args.length ||
                        ('Argument number mismatch: ' + args.length + ' vs ' + t_args.length), ast);
                    var arguments = new Array(args.length);
                    for (var i = 0; i < args.length; ++i) {
                        var tmp = check(args[i], env);
                        if (t_args[i].type === types.LocationVariable) {
                            assert((tmp.type === types.LocationVariable) ||
                                ('Argument #' + i + ' is not LocationVariable: ' + tmp.type), args[i]);
                        }
                        if (t_args[i].type === types.TypeVariable) {
                            assert((tmp.type !== types.LocationVariable) ||
                                ('Argument #' + i + ' cannot be a LocationVariable'), args[i]);
                        }
                        arguments[i] = tmp;
                    }
                    return new DefinitionType(id, arguments, typedef);
                };
            case AST.TAGGED:
                return function (ast, env) {
                    var sum = new SumType();
                    var tag = ast.tag;
                    var exp = check(ast.exp, env);
                    sum.add(tag, exp);
                    if (exp.type === types.BangType) {
                        sum = new BangType(sum);
                    }
                    return sum;
                };
            case AST.TUPLE_TYPE:
                return function (ast, env) {
                    var rec = new TupleType();
                    var bang = true;
                    for (var i = 0; i < ast.exp.length; ++i) {
                        var value = check(ast.exp[i], env);
                        rec.add(value);
                        if (value.type !== types.BangType)
                            bang = false;
                    }
                    if (bang)
                        rec = new BangType(rec);
                    return rec;
                };
            case AST.SHARE:
                return function (ast, env) {
                    var cap = check(ast.type, env);
                    var left = check(ast.a, env);
                    var right = check(ast.b, env);
                    var table = checkConformance(env, cap, left, right);
                    var res = table !== null;
                    assert(ast.value === res || ('Unexpected Result, got ' + res + ' expecting ' + ast.value), ast);
                    return table;
                };
            case AST.RELY_TYPE:
                return function (ast, env) {
                    var rely = check(ast.left, env);
                    var guarantee = check(ast.right, env);
                    return new RelyType(rely, guarantee);
                };
            case AST.GUARANTEE_TYPE:
                return function (ast, env) {
                    var guarantee = check(ast.left, env);
                    var rely = check(ast.right, env);
                    return new GuaranteeType(guarantee, rely);
                };
            case AST.REF_TYPE:
                return function (ast, env) {
                    var id = ast.text;
                    var loc = env.getTypeByName(id);
                    assert((loc !== undefined && loc.type === types.LocationVariable) ||
                        ('Unknow Location Variable ' + id), ast);
                    return new ReferenceType(loc.copy(env.getNameIndex(id)));
                };
            case AST.EXISTS_TYPE:
            case AST.FORALL:
            case AST.FORALL_TYPE:
                return (function (ctr) {
                    return function (ast, env) {
                        var id = ast.id;
                        var variable;
                        var bound;
                        if (isTypeVariableName(id)) {
                            bound = !ast.bound ?
                                TopType :
                                check(ast.bound, new Gamma(env.getTypeDef(), null));
                            variable = new TypeVariable(id, 0, bound);
                        }
                        else {
                            variable = new LocationVariable(id, 0);
                            bound = null;
                        }
                        var e = env.newScope(id, variable, bound);
                        var type = check(ast.exp, e);
                        return new ctr(variable, type, bound);
                    };
                })(kind === AST.EXISTS_TYPE ? ExistsType : ForallType);
            case AST.NONE_TYPE:
                return function (ast, env) {
                    return NoneType;
                };
            case AST.TOP_TYPE:
                return function (ast, env) {
                    return TopType;
                };
            case AST.BANG_TYPE:
                return function (ast, env) {
                    return new BangType(check(ast.type, env));
                };
            case AST.FUN_TYPE:
                return function (ast, env) {
                    return new FunctionType(check(ast.arg, env), check(ast.exp, env));
                };
            case AST.CAP_TYPE:
                return function (ast, env) {
                    var id = ast.id;
                    var loc = env.getTypeByName(id);
                    assert((loc !== undefined && loc.type === types.LocationVariable) ||
                        ('Unknow Location Variable ' + id), ast);
                    return new CapabilityType(loc.copy(env.getNameIndex(id)), check(ast.type, env));
                };
            case AST.STACKED_TYPE:
                return function (ast, env) {
                    return new StackedType(check(ast.left, env), check(ast.right, env));
                };
            case AST.RECORD_TYPE:
                return function (ast, env) {
                    var rec = new RecordType();
                    for (var i = 0; i < ast.exp.length; ++i) {
                        var field = ast.exp[i];
                        var id = field.id;
                        var value = check(field.exp, env);
                        assert(rec.add(id, value) ||
                            ("Duplicated field '" + id + "' in '" + rec + "'"), field);
                    }
                    return rec;
                };
            case AST.PRIMITIVE_TYPE:
                return function (ast, env) {
                    return new PrimitiveType(ast.text);
                };
            default:
                return function (ast, env) {
                    error("Not expecting " + ast.kind);
                };
        }
    };
    var checkProgram = function (ast, check) {
        error((ast.kind === AST.PROGRAM) || 'Unexpected AST node');
        var typedef = new TypeDefinition();
        var env = new Gamma(typedef, null);
        if (ast.typedefs !== null) {
            for (var i = 0; i < ast.typedefs.length; ++i) {
                var it = ast.typedefs[i];
                var args = [];
                var pars = it.pars;
                if (pars !== null) {
                    args = new Array(pars.length);
                    for (var j = 0; j < pars.length; ++j) {
                        var n = pars[j];
                        args[j] = isTypeVariableName(n) ?
                            new TypeVariable(n, (pars.length - j - 1), null) :
                            new LocationVariable(n, (pars.length - j - 1));
                    }
                }
                assert(typedef.addType(it.id, args)
                    || ('Duplicated typedef: ' + it.id), it);
            }
            for (var i = 0; i < ast.typedefs.length; ++i) {
                var type = ast.typedefs[i];
                var tmp_env = env;
                var args = typedef.getType(type.id);
                if (args !== null) {
                    for (var j = 0; j < args.length; ++j) {
                        tmp_env = tmp_env.newScope(args[j].name(), args[j], null);
                    }
                }
                assert(typedef.addDefinition(type.id, check(type.type, tmp_env))
                    || ('Duplicated typedef: ' + type.id), type);
            }
            for (var i = 0; i < ast.typedefs.length; ++i) {
                var type = ast.typedefs[i];
                var x = typedef.getDefinition(type.id);
                var set = new Set();
                while (x.type === types.DefinitionType) {
                    set.add(x.toString(false));
                    x = unfoldDefinition(x);
                    assert(!set.has(x.toString(false))
                        || ('Infinite typedef (i.e. bottom type): ' + type.id), type);
                }
            }
        }
        var exps = ast.exp;
        for (var i = 0; i < exps.length; ++i) {
            check(exps[i], env);
        }
        return NoneType;
    };
    var buildChecker = function (inspector) {
        var map = new Map();
        var aux = function (ast, env) {
            if (!map.has(ast.kind))
                error('Error @buildChecker Not expecting ' + ast.kind);
            return map.get(ast.kind)(ast, env);
        };
        var tmp = aux;
        if (inspector) {
            tmp = function (ast, env) {
                return inspector(ast, env, aux);
            };
        }
        for (var i in AST) {
            error(!map.has(i) || ('Error @buildChecker, duplication: ' + i));
            map.set(i, setupAST(i, tmp));
        }
        return tmp;
    };
    var type_info = [];
    var inspector = function (ast, env, c) {
        var info = { ast: ast, env: env };
        type_info.push(info);
        var res = c(ast, env);
        info.res = res;
        if (ast.kind === AST.SHARE) {
            return UnitType;
        }
        return res;
    };
    var checker = buildChecker(inspector);
    exports.check = function (ast, log) {
        type_info = [];
        var start = new Date().getTime();
        try {
            return checkProgram(ast, checker);
        }
        finally {
            if (log) {
                log.diff = (new Date().getTime()) - start;
                log.info = type_info;
            }
        }
    };
    return exports;
})(AST.kinds, TypeChecker);
