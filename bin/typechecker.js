// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
var TypeChecker;
(function (TypeChecker) {
    var Unit = new TypeChecker.BangType(new TypeChecker.RecordType());
    var None = new TypeChecker.NoneType();
    var Top = new TypeChecker.TopType();
    function assert(msg) {
        if (typeof (msg) === 'boolean' && msg)
            return;
        throw new ErrorWrapper(msg.message, 'Type Error', msg.ast);
    }
    TypeChecker.assert = assert;
    ;
    var ERROR;
    (function (ERROR) {
        var Message = (function () {
            function Message(message, ast) {
                this.message = message;
                this.ast = ast;
            }
            return Message;
        })();
        ERROR.Message = Message;
        ;
        function UnknownType(id, ast) {
            return new Message('Unknown type ' + id, ast);
        }
        ERROR.UnknownType = UnknownType;
        ;
        function UnknownLocation(id, ast) {
            return new Message('Unknown location variable ' + id, ast);
        }
        ERROR.UnknownLocation = UnknownLocation;
        ;
        function UnexpectedResult(got, expected, ast) {
            return new Message('Unexpected result, got ' + got + ' expecting ' + expected, ast);
        }
        ERROR.UnexpectedResult = UnexpectedResult;
        ;
        function DuplicatedTypedef(id, ast) {
            return new Message('Duplicated typedef: ' + id, ast);
        }
        ERROR.DuplicatedTypedef = DuplicatedTypedef;
        ;
        function DuplicatedTag(id, ast) {
            return new Message('Duplicated tag: ' + id, ast);
        }
        ERROR.DuplicatedTag = DuplicatedTag;
        ;
        function InvalidSubstitution(t, ast) {
            return new Message('Can only substitute a Type/LocationVariable, got:  ' + t.type, ast);
        }
        ERROR.InvalidSubstitution = InvalidSubstitution;
        ;
        function DuplicatedField(id, r, ast) {
            return new Message('Duplicated field "' + id + '" in ' + r, ast);
        }
        ERROR.DuplicatedField = DuplicatedField;
        ;
        function ArgumentMismatch(got, expected, ast) {
            return new Message('Argument number mismatch, got: ' + got + ' expecting ' + expected, ast);
        }
        ERROR.ArgumentMismatch = ArgumentMismatch;
        ;
        function ExpectingLocation(i, t, ast) {
            return new Message('Argument #' + i + ' must be a LocationVariable, got: ' + t.type, ast);
        }
        ERROR.ExpectingLocation = ExpectingLocation;
        ;
        function UnexpectedLocation(i, ast) {
            return new Message('Argument #' + i + ' cannot be a LocationVariable.', ast);
        }
        ERROR.UnexpectedLocation = UnexpectedLocation;
        ;
    })(ERROR || (ERROR = {}));
    function isTypeVariableName(n) {
        return n[0] === n[0].toUpperCase();
    }
    ;
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
                s = new TypeChecker.RelyType(TypeChecker.shift(s.rely(), 0, 1), gs.inner());
                p = new TypeChecker.RelyType(TypeChecker.shift(p.rely(), 0, 1), gs.inner());
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
                return step(new TypeChecker.RelyType(s.rely(), t), p, q, isLeft);
            }
            if (s.type === TypeChecker.types.RelyType && p.type === TypeChecker.types.RelyType && TypeChecker.subtype(s.rely(), p.rely())) {
                var gs = s.guarantee();
                var gp = p.guarantee();
                if (gs.type !== TypeChecker.types.GuaranteeType) {
                    gs = new TypeChecker.GuaranteeType(gs, None);
                }
                if (gp.type !== TypeChecker.types.GuaranteeType) {
                    gp = new TypeChecker.GuaranteeType(gp, None);
                }
                if (TypeChecker.subtype(gp.guarantee(), gs.guarantee())) {
                    return [R(gs.rely(), gp.rely())];
                }
            }
            return null;
        }
        else {
            if (TypeChecker.equals(s, p)) {
                return [R(None, None)];
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
                p = new TypeChecker.RelyType(TypeChecker.shift(p.rely(), 0, 1), p.guarantee().inner());
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
                    return [R(b, None)];
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
    ;
    var matchExp = {
        Program: function (ast) { return function (c, _) {
            // ignores old environment, this is a new program!
            var typedef = new TypeChecker.TypeDefinition();
            var env = new TypeChecker.Gamma(typedef, null);
            if (ast.typedefs !== null) {
                for (var i = 0; i < ast.typedefs.length; ++i) {
                    var it = ast.typedefs[i];
                    var args_1 = [];
                    var pars = it.pars;
                    if (pars !== null) {
                        args_1 = new Array(pars.length);
                        for (var j = 0; j < pars.length; ++j) {
                            var n = pars[j];
                            args_1[j] = isTypeVariableName(n) ?
                                new TypeChecker.TypeVariable(n, (pars.length - j - 1), null) :
                                new TypeChecker.LocationVariable(n, (pars.length - j - 1));
                        }
                    }
                    assert(typedef.addType(it.id, args_1) || ERROR.DuplicatedTypedef(it.id, it));
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
                        || ERROR.DuplicatedTypedef(type.id, type));
                }
            }
            var tmp = [];
            for (var _i = 0, _a = ast.exp; _i < _a.length; _i++) {
                var exp = _a[_i];
                tmp = tmp.concat(c.checkExp(exp, env));
            }
            return tmp;
        }; },
        Share: function (ast) { return function (c, env) {
            var cap = c.checkType(ast.type, env);
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var table = checkConformance(env, cap, left, right);
            var res = table !== null;
            assert(ast.value === res || ERROR.UnexpectedResult(res, ast.value, ast));
            return [[ast, table]];
        }; },
        Subtype: function (ast) { return function (c, env) {
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var s = TypeChecker.subtype(left, right);
            assert(s == ast.value || ERROR.UnexpectedResult(s, ast.value, ast));
            return [];
        }; },
        Equals: function (ast) { return function (c, env) {
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var s = TypeChecker.equals(left, right);
            assert(s == ast.value || ERROR.UnexpectedResult(s, ast.value, ast));
            return [];
        }; },
        Forall: function (ast) { return function (c, env) {
            var id = ast.id;
            var variable;
            var bound;
            if (isTypeVariableName(id)) {
                bound = !ast.bound ?
                    Top :
                    c.checkType(ast.bound, new TypeChecker.Gamma(env.getTypeDef(), null));
                variable = new TypeChecker.TypeVariable(id, 0, bound);
            }
            else {
                variable = new TypeChecker.LocationVariable(id, 0);
                bound = null;
            }
            var e = env.newScope(id, variable, bound);
            return c.checkExp(ast.exp, e);
        }; },
    };
    var matchType = {
        Substitution: function (ast) { return function (c, env) {
            var type = c.checkType(ast.type, env);
            var to = c.checkType(ast.to, env);
            var from = c.checkType(ast.from, env);
            assert((from.type === TypeChecker.types.LocationVariable || from.type === TypeChecker.types.TypeVariable)
                || ERROR.InvalidSubstitution(from, ast.from));
            return TypeChecker.substitution(type, from, to);
        }; },
        _aux_: function (ctr, ast) { return function (c, env) {
            var id = ast.id;
            var variable;
            var bound;
            if (isTypeVariableName(id)) {
                bound = !ast.bound ?
                    Top :
                    c.checkType(ast.bound, new TypeChecker.Gamma(env.getTypeDef(), null));
                variable = new TypeChecker.TypeVariable(id, 0, bound);
            }
            else {
                variable = new TypeChecker.LocationVariable(id, 0);
                bound = null;
            }
            var e = env.newScope(id, variable, bound);
            var type = c.checkType(ast.exp, e);
            return new ctr(variable, type, bound);
        }; },
        Exists: function (ast) { return this._aux_(TypeChecker.ExistsType, ast); },
        Forall: function (ast) { return this._aux_(TypeChecker.ForallType, ast); },
        Stacked: function (ast) { return function (c, env) {
            return new TypeChecker.StackedType(c.checkType(ast.left, env), c.checkType(ast.right, env));
        }; },
        Rely: function (ast) { return function (c, env) {
            var rely = c.checkType(ast.left, env);
            var guarantee = c.checkType(ast.right, env);
            return new TypeChecker.RelyType(rely, guarantee);
        }; },
        Guarantee: function (ast) { return function (c, env) {
            var guarantee = c.checkType(ast.left, env);
            var rely = c.checkType(ast.right, env);
            return new TypeChecker.GuaranteeType(guarantee, rely);
        }; },
        Sum: function (ast) { return function (c, env) {
            var sum = new TypeChecker.SumType();
            for (var _i = 0, _a = ast.sums; _i < _a.length; _i++) {
                var t = _a[_i];
                assert(sum.add(t.tag, c.checkType(t.type, env)) ||
                    ERROR.DuplicatedTag(t.tag, t));
            }
            return sum;
        }; },
        Star: function (ast) { return function (c, env) {
            var star = new TypeChecker.StarType();
            for (var _i = 0, _a = ast.types; _i < _a.length; _i++) {
                var t = _a[_i];
                star.add(c.checkType(t, env));
            }
            return star;
        }; },
        Alternative: function (ast) { return function (c, env) {
            var alt = new TypeChecker.AlternativeType();
            for (var _i = 0, _a = ast.types; _i < _a.length; _i++) {
                var t = _a[_i];
                alt.add(c.checkType(t, env));
            }
            return alt;
        }; },
        Intersection: function (ast) { return function (c, env) {
            var alt = new TypeChecker.IntersectionType();
            for (var _i = 0, _a = ast.types; _i < _a.length; _i++) {
                var t = _a[_i];
                alt.add(c.checkType(t, env));
            }
            return alt;
        }; },
        Function: function (ast) { return function (c, env) {
            return new TypeChecker.FunctionType(c.checkType(ast.arg, env), c.checkType(ast.exp, env));
        }; },
        Capability: function (ast) { return function (c, env) {
            var id = ast.id;
            var loc = env.getTypeByName(id);
            assert((loc !== undefined && loc.type === TypeChecker.types.LocationVariable) ||
                ERROR.UnknownLocation(id, ast));
            return new TypeChecker.CapabilityType(loc.copy(env.getNameIndex(id)), c.checkType(ast.type, env));
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
                return new TypeChecker.DefinitionType(label, [], typedef);
            assert(ERROR.UnknownType(label, ast));
        }; },
        Reference: function (ast) { return function (c, env) {
            var id = ast.text;
            var loc = env.getTypeByName(id);
            assert((loc !== undefined && loc.type === TypeChecker.types.LocationVariable) ||
                ERROR.UnknownLocation(id, ast));
            return new TypeChecker.ReferenceType(loc.copy(env.getNameIndex(id)));
        }; },
        Bang: function (ast) { return function (c, env) {
            return new TypeChecker.BangType(c.checkType(ast.type, env));
        }; },
        Record: function (ast) { return function (c, env) {
            var rec = new TypeChecker.RecordType();
            for (var i = 0; i < ast.exp.length; ++i) {
                var field = ast.exp[i];
                var id = field.id;
                var value = c.checkType(field.exp, env);
                assert(rec.add(id, value) || ERROR.DuplicatedField(id, rec, field));
            }
            return rec;
        }; },
        Tuple: function (ast) { return function (c, env) {
            var rec = new TypeChecker.TupleType();
            for (var _i = 0, _a = ast.exp; _i < _a.length; _i++) {
                var exp = _a[_i];
                rec.add(c.checkType(exp, env));
            }
            return rec;
        }; },
        Tagged: function (ast) { return function (c, env) {
            var sum = new TypeChecker.SumType();
            var exp = c.checkType(ast.type, env);
            sum.add(ast.tag, exp);
            return sum;
        }; },
        Top: function (ast) { return function (c, env) {
            return Top;
        }; },
        Definition: function (ast) { return function (c, env) {
            var typedef = env.getTypeDef();
            var id = ast.name;
            var args = ast.args;
            var t_args = typedef.getType(id);
            assert(t_args !== undefined || ERROR.UnknownType(id, ast));
            assert(t_args.length === args.length || ERROR.ArgumentMismatch(args.length, t_args.length, ast));
            var arguments = new Array(args.length);
            for (var i = 0; i < args.length; ++i) {
                var tmp = c.checkType(args[i], env);
                if (t_args[i].type === TypeChecker.types.LocationVariable) {
                    assert((tmp.type === TypeChecker.types.LocationVariable) ||
                        ERROR.ExpectingLocation(i, tmp, args[i]));
                }
                if (t_args[i].type === TypeChecker.types.TypeVariable) {
                    assert((tmp.type !== TypeChecker.types.LocationVariable) ||
                        ERROR.UnexpectedLocation(i, args[i]));
                }
                arguments[i] = tmp;
            }
            return new TypeChecker.DefinitionType(id, arguments, typedef);
        }; },
        Primitive: function (ast) { return function (c, env) {
            return new TypeChecker.PrimitiveType(ast.text);
        }; },
        None: function (ast) { return function (c, env) {
            return None;
        }; },
    };
    function checker(ast) {
        var log = {
            time: (new Date().getTime()),
            info: []
        };
        var c = {
            checkExp: function (ast, env) {
                return (ast.match(matchExp))(c, env);
            },
            checkType: function (ast, env) {
                return (ast.match(matchType))(c, env);
            },
        };
        try {
            log.info = c.checkExp(ast, null);
            return log;
        }
        finally {
            log.time = (new Date().getTime()) - log.time;
        }
    }
    TypeChecker.checker = checker;
    ;
})(TypeChecker || (TypeChecker = {}));
;
