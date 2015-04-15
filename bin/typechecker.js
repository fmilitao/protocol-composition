// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
var TypeChecker;
(function (TypeChecker) {
    var FunctionType = TypeChecker.fct.FunctionType;
    var BangType = TypeChecker.fct.BangType;
    var SumType = TypeChecker.fct.SumType;
    var StarType = TypeChecker.fct.StarType;
    var AlternativeType = TypeChecker.fct.AlternativeType;
    var IntersectionType = TypeChecker.fct.IntersectionType;
    var ForallType = TypeChecker.fct.ForallType;
    var ExistsType = TypeChecker.fct.ExistsType;
    var RecordType = TypeChecker.fct.RecordType;
    var TupleType = TypeChecker.fct.TupleType;
    var ReferenceType = TypeChecker.fct.ReferenceType;
    var StackedType = TypeChecker.fct.StackedType;
    var CapabilityType = TypeChecker.fct.CapabilityType;
    var LocationVariable = TypeChecker.fct.LocationVariable;
    var TypeVariable = TypeChecker.fct.TypeVariable;
    var PrimitiveType = TypeChecker.fct.PrimitiveType;
    var RelyType = TypeChecker.fct.RelyType;
    var DefinitionType = TypeChecker.fct.DefinitionType;
    var GuaranteeType = TypeChecker.fct.GuaranteeType;
    var UnitType = new BangType(new RecordType());
    var NoneType = new TypeChecker.fct.NoneType();
    var TopType = new TypeChecker.fct.TopType();
    var isTypeVariableName = function (n) {
        return n[0] === n[0].toUpperCase();
    };
    var unifyRely = function (id, step, state) {
        switch (step.type) {
            case TypeChecker.types.ExistsType:
                id;
                return unifyRely(TypeChecker.shift(id, 0, 1), step.inner(), TypeChecker.shift(state, 0, 1));
            case TypeChecker.types.RelyType:
                return TypeChecker.unify(id, step.rely(), state);
            case TypeChecker.types.AlternativeType: {
                var is = step.inner();
                for (var i = 0; i < is.length; ++i) {
                    var tmp = unifyRely(id, is[i], state);
                    if (tmp !== false)
                        return tmp;
                }
                return false;
            }
            case TypeChecker.types.IntersectionType: {
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
                        if (!TypeChecker.equals(res, tmp))
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
            case TypeChecker.types.ForallType:
                return unifyGuarantee(TypeChecker.shift(id, 0, 1), step.inner(), TypeChecker.shift(state, 0, 1));
            case TypeChecker.types.GuaranteeType:
                return TypeChecker.unify(id, step.guarantee(), state);
            case TypeChecker.types.AlternativeType: {
                var is = step.inner();
                for (var i = 0; i < is.length; ++i) {
                    var tmp = unifyGuarantee(id, is[i], state);
                    if (tmp !== false)
                        return tmp;
                }
                return false;
            }
            case TypeChecker.types.IntersectionType: {
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
                        if (!TypeChecker.equals(res, tmp))
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
            if (TypeChecker.subtype(w.s, v.s) &&
                TypeChecker.subtype(v.p, w.p) &&
                TypeChecker.subtype(v.q, w.q))
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
        s = TypeChecker.unfold(s);
        p = TypeChecker.unfold(p);
        var res = singleStep(s, p, q, isLeft);
        if (res !== null)
            return res;
        if (s.type === TypeChecker.types.AlternativeType) {
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
        if (p.type === TypeChecker.types.IntersectionType) {
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
        if (p.type === TypeChecker.types.AlternativeType) {
            var pp = p.inner();
            for (var i = 0; i < pp.length; ++i) {
                var tmp = step(s, pp[i], q, isLeft);
                if (tmp !== null)
                    return tmp;
            }
        }
        if (s.type === TypeChecker.types.IntersectionType) {
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
        if (p.type === TypeChecker.types.NoneType) {
            return [];
        }
        if (TypeChecker.isProtocol(s)) {
            if (s.type === TypeChecker.types.ExistsType && p.type === TypeChecker.types.ExistsType) {
                if (s.id().type !== p.id().type)
                    return null;
                return step(s.inner(), p.inner(), TypeChecker.shift(q, 0, 1), isLeft);
            }
            if (s.type === TypeChecker.types.RelyType && s.guarantee().type === TypeChecker.types.ForallType &&
                p.type === TypeChecker.types.RelyType && p.guarantee().type === TypeChecker.types.ForallType) {
                var gs = s.guarantee();
                var gp = p.guarantee();
                if (gs.id().type !== gp.id().type)
                    return null;
                s = new RelyType(TypeChecker.shift(s.rely(), 0, 1), gs.inner());
                p = new RelyType(TypeChecker.shift(p.rely(), 0, 1), gs.inner());
                q = TypeChecker.shift(q, 0, 1);
                return step(s, p, q, isLeft);
            }
            if (s.type === TypeChecker.types.RelyType && s.guarantee().type === TypeChecker.types.ForallType &&
                p.type === TypeChecker.types.RelyType && p.guarantee().type !== TypeChecker.types.ForallType) {
                var b = s.guarantee();
                var i = b.id();
                var t = b.inner();
                b = p.guarantee();
                if (b.type === TypeChecker.types.GuaranteeType)
                    b = b.guarantee();
                var x = unifyGuarantee(i, t, TypeChecker.shift(b, 0, 1));
                if (x === false)
                    return null;
                if (x !== true) {
                    t = TypeChecker.substitution(t, i, x);
                }
                t = TypeChecker.shift(t, 0, -1);
                return step(new RelyType(s.rely(), t), p, q, isLeft);
            }
            if (s.type === TypeChecker.types.RelyType && p.type === TypeChecker.types.RelyType && TypeChecker.subtype(s.rely(), p.rely())) {
                var gs = s.guarantee();
                var gp = p.guarantee();
                if (gs.type !== TypeChecker.types.GuaranteeType) {
                    gs = new GuaranteeType(gs, NoneType);
                }
                if (gp.type !== TypeChecker.types.GuaranteeType) {
                    gp = new GuaranteeType(gp, NoneType);
                }
                if (TypeChecker.subtype(gp.guarantee(), gs.guarantee())) {
                    return [R(gs.rely(), gp.rely())];
                }
            }
            return null;
        }
        else {
            if (TypeChecker.equals(s, p)) {
                return [R(NoneType, NoneType)];
            }
            if (p.type === TypeChecker.types.ExistsType) {
                var i = p.id();
                var t = p.inner();
                var x = unifyRely(i, t, TypeChecker.shift(s, 0, 1));
                if (x === false)
                    return null;
                if (x !== true) {
                    t = TypeChecker.substitution(t, i, x);
                }
                t = TypeChecker.shift(t, 0, -1);
                return step(s, t, q, isLeft);
            }
            if (p.type === TypeChecker.types.RelyType && p.guarantee().type === TypeChecker.types.ForallType) {
                p = new RelyType(TypeChecker.shift(p.rely(), 0, 1), p.guarantee().inner());
                q = TypeChecker.shift(q, 0, 1);
                s = TypeChecker.shift(s, 0, 1);
                return step(s, p, q, isLeft);
            }
            if (p.type === TypeChecker.types.RelyType && TypeChecker.subtype(s, p.rely())) {
                var b = p.guarantee();
                if (b.type === TypeChecker.types.GuaranteeType) {
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
        var set = TypeChecker.indexSet(s);
        TypeChecker.indexSet(a).forEach(function (v) { set.add(v); });
        TypeChecker.indexSet(b).forEach(function (v) { set.add(v); });
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
                    s = TypeChecker.shift(s, i, v[i]);
                    a = TypeChecker.shift(a, i, v[i]);
                    b = TypeChecker.shift(b, i, v[i]);
                }
            }
        }
        return [s, a, b];
    };
    var matchExp = {
        TypeDef: function (x) { return TypeChecker.assert(false, x); },
        Program: function (ast) { return function (c, _) {
            // ignores old environment, this is a new program!
            var typedef = new TypeChecker.TypeDefinition();
            var env = new TypeChecker.Gamma(typedef, null);
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
                    TypeChecker.assert(typedef.addType(it.id, args)
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
                    TypeChecker.assert(typedef.addDefinition(type.id, c.checkType(type.type, tmp_env))
                        || ('Duplicated typedef: ' + type.id), type);
                }
                for (var i = 0; i < ast.typedefs.length; ++i) {
                    var type = ast.typedefs[i];
                    var x = typedef.getDefinition(type.id);
                    var set = new Set();
                    while (x.type === TypeChecker.types.DefinitionType) {
                        set.add(x.toString(false));
                        x = TypeChecker.unfoldDefinition(x);
                        TypeChecker.assert(!set.has(x.toString(false))
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
            TypeChecker.assert(ast.value === res || ('Unexpected Result, got ' + res + ' expecting ' + ast.value), ast);
            return table;
        }; },
        Subtype: function (ast) { return function (c, env) {
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var s = TypeChecker.subtype(left, right);
            TypeChecker.assert(s == ast.value || ('Unexpected Result, got ' + s + ' expecting ' + ast.value), ast);
            return left;
        }; },
        Equals: function (ast) { return function (c, env) {
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var s = TypeChecker.equals(left, right);
            TypeChecker.assert(s == ast.value || ('Unexpected Result, got ' + s + ' expecting ' + ast.value), ast);
            return left;
        }; },
        Forall: function (ast) { return function (c, env) {
            var id = ast.id;
            var variable;
            var bound;
            if (isTypeVariableName(id)) {
                bound = !ast.bound ?
                    TopType :
                    c.checkType(ast.bound, new TypeChecker.Gamma(env.getTypeDef(), null));
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
        Substitution: function (ast) { return function (c, env) {
            var type = c.checkType(ast.type, env);
            var to = c.checkType(ast.to, env);
            var from = c.checkType(ast.from, env);
            TypeChecker.assert((from.type === TypeChecker.types.LocationVariable || from.type === TypeChecker.types.TypeVariable)
                || ("Can only substitute a Type/LocationVariable, got: " + from.type), ast.from);
            return TypeChecker.substitution(type, from, to);
        }; },
        _aux_: function (ctr, ast) { return function (c, env) {
            var id = ast.id;
            var variable;
            var bound;
            if (isTypeVariableName(id)) {
                bound = !ast.bound ?
                    TopType :
                    c.checkType(ast.bound, new TypeChecker.Gamma(env.getTypeDef(), null));
                variable = new TypeVariable(id, 0, bound);
            }
            else {
                variable = new LocationVariable(id, 0);
                bound = null;
            }
            var e = env.newScope(id, variable, bound);
            var type = c.checkType(ast.exp, e);
            return new ctr(variable, type, bound);
        }; },
        Exists: function (ast) { return matchType._aux_(ExistsType, ast); },
        Forall: function (ast) { return matchType._aux_(ForallType, ast); },
        Stacked: function (ast) { return function (c, env) {
            return new StackedType(c.checkType(ast.left, env), c.checkType(ast.right, env));
        }; },
        Rely: function (ast) { return function (c, env) {
            var rely = c.checkType(ast.left, env);
            var guarantee = c.checkType(ast.right, env);
            return new RelyType(rely, guarantee);
        }; },
        Guarantee: function (ast) { return function (c, env) {
            var guarantee = c.checkType(ast.left, env);
            var rely = c.checkType(ast.right, env);
            return new GuaranteeType(guarantee, rely);
        }; },
        Sum: function (ast) { return function (c, env) {
            var sum = new SumType();
            for (var i = 0; i < ast.sums.length; ++i) {
                var tag = ast.sums[i].tag;
                TypeChecker.assert(sum.add(tag, c.checkType(ast.sums[i].exp, env)) ||
                    "Duplicated tag: " + tag, ast.sums[i]);
            }
            return sum;
        }; },
        Star: function (ast) { return function (c, env) {
            var star = new StarType();
            for (var i = 0; i < ast.types.length; ++i) {
                star.add(c.checkType(ast.types[i], env));
            }
            return star;
        }; },
        Alternative: function (ast) { return function (c, env) {
            var alt = new AlternativeType();
            for (var i = 0; i < ast.types.length; ++i) {
                alt.add(c.checkType(ast.types[i], env));
            }
            return alt;
        }; },
        Intersection: function (ast) { return function (c, env) {
            var alt = new IntersectionType();
            for (var i = 0; i < ast.types.length; ++i) {
                alt.add(c.checkType(ast.types[i], env));
            }
            return alt;
        }; },
        Function: function (ast) { return function (c, env) {
            return new FunctionType(c.checkType(ast.arg, env), c.checkType(ast.exp, env));
        }; },
        Capability: function (ast) { return function (c, env) {
            var id = ast.id;
            var loc = env.getTypeByName(id);
            TypeChecker.assert((loc !== undefined && loc.type === TypeChecker.types.LocationVariable) ||
                ('Unknow Location Variable ' + id), ast);
            return new CapabilityType(loc.copy(env.getNameIndex(id)), c.checkType(ast.type, env));
        }; },
        Name: function (ast) { return function (c, env) {
            var label = ast.text;
            var typedef = env.getTypeDef();
            var tmp = env.getTypeByName(label);
            if (tmp !== undefined &&
                (tmp.type === TypeChecker.types.TypeVariable ||
                    tmp.type === TypeChecker.types.LocationVariable)) {
                return tmp.copy(env.getNameIndex(label));
            }
            var lookup_args = typedef.getType(label);
            if (lookup_args !== undefined && lookup_args.length === 0)
                return new DefinitionType(label, [], typedef);
            TypeChecker.assert('Unknown type ' + label, ast);
        }; },
        Reference: function (ast) { return function (c, env) {
            var id = ast.text;
            var loc = env.getTypeByName(id);
            TypeChecker.assert((loc !== undefined && loc.type === TypeChecker.types.LocationVariable) ||
                ('Unknow Location Variable ' + id), ast);
            return new ReferenceType(loc.copy(env.getNameIndex(id)));
        }; },
        Bang: function (ast) { return function (c, env) {
            return new BangType(c.checkType(ast.type, env));
        }; },
        Record: function (ast) { return function (c, env) {
            var rec = new RecordType();
            for (var i = 0; i < ast.exp.length; ++i) {
                var field = ast.exp[i];
                var id = field.id;
                var value = c.checkType(field.exp, env);
                TypeChecker.assert(rec.add(id, value) ||
                    ("Duplicated field '" + id + "' in '" + rec + "'"), field);
            }
            return rec;
        }; },
        Field: function (ast) { return TypeChecker.assert(false, ast); },
        Tuple: function (ast) { return function (c, env) {
            var rec = new TupleType();
            var bang = true;
            for (var i = 0; i < ast.exp.length; ++i) {
                var value = c.checkType(ast.exp[i], env);
                rec.add(value);
                if (value.type !== TypeChecker.types.BangType)
                    bang = false;
            }
            if (bang)
                rec = new BangType(rec);
            return rec;
        }; },
        Tagged: function (ast) { return function (c, env) {
            var sum = new SumType();
            var tag = ast.tag;
            var exp = c.checkType(ast.exp, env);
            sum.add(tag, exp);
            if (exp.type === TypeChecker.types.BangType) {
                sum = new BangType(sum);
            }
            return sum;
        }; },
        Top: function (ast) { return function (c, env) {
            return TopType;
        }; },
        Definition: function (ast) { return function (c, env) {
            var typedef = env.getTypeDef();
            var id = ast.name;
            var args = ast.args;
            var t_args = typedef.getType(id);
            TypeChecker.assert(t_args !== undefined || ('Unknown typedef: ' + id), ast);
            TypeChecker.assert(t_args.length === args.length ||
                ('Argument number mismatch: ' + args.length + ' vs ' + t_args.length), ast);
            var arguments = new Array(args.length);
            for (var i = 0; i < args.length; ++i) {
                var tmp = c.checkType(args[i], env);
                if (t_args[i].type === TypeChecker.types.LocationVariable) {
                    TypeChecker.assert((tmp.type === TypeChecker.types.LocationVariable) ||
                        ('Argument #' + i + ' is not LocationVariable: ' + tmp.type), args[i]);
                }
                if (t_args[i].type === TypeChecker.types.TypeVariable) {
                    TypeChecker.assert((tmp.type !== TypeChecker.types.LocationVariable) ||
                        ('Argument #' + i + ' cannot be a LocationVariable'), args[i]);
                }
                arguments[i] = tmp;
            }
            return new DefinitionType(id, arguments, typedef);
        }; },
        Primitive: function (ast) { return function (c, env) {
            return new PrimitiveType(ast.text);
        }; },
        None: function (ast) { return function (c, env) {
            return NoneType;
        }; },
    };
    function checker(ast, log) {
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
    }
    TypeChecker.checker = checker;
    ;
})(TypeChecker || (TypeChecker = {}));
;
