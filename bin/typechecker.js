// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
var TypeChecker;
(function (TypeChecker) {
    function assert(msg, f) {
        if (typeof (msg) === 'boolean')
            return (f === undefined ? [] : f());
        var error = new ErrorWrapper(msg.message, 'Type Error', msg.ast);
        if (f === undefined)
            throw error;
        return [error].concat(f());
    }
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
                            args_1[j] = TypeChecker.isTypeVariableName(n) ?
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
            var table = TypeChecker.checkConformance(env, cap, left, right);
            var res = table !== null;
            return assert(ast.value === res || ERROR.UnexpectedResult(res, ast.value, ast), function () { return [[ast, table]]; });
        }; },
        Subtype: function (ast) { return function (c, env) {
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var s = TypeChecker.subtype(left, right);
            return assert(s == ast.value || ERROR.UnexpectedResult(s, ast.value, ast), function () { return []; });
        }; },
        Equals: function (ast) { return function (c, env) {
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var s = TypeChecker.equals(left, right);
            return assert(s == ast.value || ERROR.UnexpectedResult(s, ast.value, ast), function () { return []; });
        }; },
        Forall: function (ast) { return function (c, env) {
            var id = ast.id;
            var variable;
            var bound;
            if (TypeChecker.isTypeVariableName(id)) {
                bound = !ast.bound ?
                    TypeChecker.Top :
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
            assert((from instanceof TypeChecker.LocationVariable) || (from instanceof TypeChecker.TypeVariable)
                || ERROR.InvalidSubstitution(from, ast.from));
            return TypeChecker.substitution(type, from, to);
        }; },
        _aux_: function (ctr, ast) { return function (c, env) {
            var id = ast.id;
            var variable;
            var bound;
            if (TypeChecker.isTypeVariableName(id)) {
                bound = !ast.bound ?
                    TypeChecker.Top :
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
            assert((loc !== undefined && (loc instanceof TypeChecker.LocationVariable)) ||
                ERROR.UnknownLocation(id, ast));
            return new TypeChecker.CapabilityType(loc.copy(env.getNameIndex(id)), c.checkType(ast.type, env));
        }; },
        Name: function (ast) { return function (c, env) {
            var label = ast.text;
            var typedef = env.getTypeDef();
            var tmp = env.getTypeByName(label);
            if (tmp !== undefined &&
                ((tmp instanceof TypeChecker.TypeVariable) ||
                    (tmp instanceof TypeChecker.LocationVariable))) {
                return tmp.copy(env.getNameIndex(label));
            }
            var lookup_args = typedef.getType(label);
            if (lookup_args !== undefined && lookup_args.length === 0)
                return new TypeChecker.RecursiveType(label, [], typedef);
            assert(ERROR.UnknownType(label, ast));
        }; },
        Reference: function (ast) { return function (c, env) {
            var id = ast.text;
            var loc = env.getTypeByName(id);
            assert((loc !== undefined && (loc instanceof TypeChecker.LocationVariable)) ||
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
            return TypeChecker.Top;
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
                if (t_args[i] instanceof TypeChecker.LocationVariable) {
                    assert((tmp instanceof TypeChecker.LocationVariable) ||
                        ERROR.ExpectingLocation(i, tmp, args[i]));
                }
                if (t_args[i] instanceof TypeChecker.TypeVariable) {
                    assert(!(tmp instanceof TypeChecker.LocationVariable) ||
                        ERROR.UnexpectedLocation(i, args[i]));
                }
                arguments[i] = tmp;
            }
            return new TypeChecker.RecursiveType(id, arguments, typedef);
        }; },
        Primitive: function (ast) { return function (c, env) {
            return new TypeChecker.PrimitiveType(ast.text);
        }; },
        None: function (ast) { return function (c, env) {
            return TypeChecker.None;
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
