// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
var TypeChecker = (function (exports) {
    //var AST: any = null; // FIXME!!!!
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
                id;
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
    var matchExp = {
        TypeDef: function (x) { return assert(false, x); },
        Program: function (ast) { return function (c, _) {
            // ignores old environment, this is a new program!
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
                    assert(typedef.addDefinition(type.id, c.checkType(type.type, tmp_env))
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
            for (var _i = 0, _a = ast.exp; _i < _a.length; _i++) {
                var exp = _a[_i];
                c.checkExp(exp, env);
            }
            return NoneType;
        }; },
        Share: function (ast) { return function (c, env) {
            var cap = c.checkType(ast.type, env);
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var table = checkConformance(env, cap, left, right);
            var res = table !== null;
            assert(ast.value === res || ('Unexpected Result, got ' + res + ' expecting ' + ast.value), ast);
            return table;
        }; },
        Subtype: function (ast) { return function (c, env) {
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var s = subtype(left, right);
            assert(s == ast.value || ('Unexpected Result, got ' + s + ' expecting ' + ast.value), ast);
            return left;
        }; },
        Equals: function (ast) { return function (c, env) {
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var s = equals(left, right);
            assert(s == ast.value || ('Unexpected Result, got ' + s + ' expecting ' + ast.value), ast);
            return left;
        }; },
        Forall: function (ast) { return function (c, env) {
            var id = ast.id;
            var variable;
            var bound;
            if (isTypeVariableName(id)) {
                bound = !ast.bound ?
                    TopType :
                    c.checkType(ast.bound, new Gamma(env.getTypeDef(), null));
                variable = new TypeVariable(id, 0, bound);
            }
            else {
                variable = new LocationVariable(id, 0);
                bound = null;
            }
            var e = env.newScope(id, variable, bound);
            var type = c.checkExp(ast.exp, e);
            return new ForallType(variable, type, bound);
        }; },
    };
    var matchType = {
        Substitution: function (x) { return null; },
        Exists: function (x) { return null; },
        Forall: function (x) { return null; },
        Stacked: function (x) { return null; },
        Rely: function (x) { return null; },
        Guarantee: function (x) { return null; },
        Sum: function (x) { return null; },
        Star: function (x) { return null; },
        Alternative: function (x) { return null; },
        Intersection: function (x) { return null; },
        Function: function (x) { return null; },
        Capability: function (x) { return null; },
        Name: function (x) { return null; },
        Reference: function (x) { return null; },
        Bang: function (x) { return null; },
        Record: function (x) { return null; },
        Field: function (x) { return null; },
        Tuple: function (x) { return null; },
        Tagged: function (x) { return null; },
        Top: function (x) { return null; },
        Definition: function (x) { return null; },
        Primitive: function (ast) { return function (c, env) {
            return new PrimitiveType(ast.text);
        }; },
        None: function (ast) { return function (c, env) {
            return NoneType;
        }; },
    };
    exports.check = function (ast, log) {
        //type_info = []; // reset
        var start = new Date().getTime();
        var c = {
            checkExp: function (ast, env) {
                return (ast.match(matchExp))(c, env);
            },
            checkType: function (ast, env) {
                return (ast.match(matchType))(c, env);
            },
        };
        try {
            return c.checkExp(ast, c);
        }
        finally {
            if (log) {
                log.diff = (new Date().getTime()) - start;
            }
        }
    };
    return exports;
})(TypeChecker);
