// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

module TypeChecker {

    /**
     * Use as:
     *        assert( BOOLEAN_CONDITION || ERROR_MSG( STRING, AST ) );
     * so as to only compute ERROR_MSG if BOOLEAN_CONDITION is false.
     */
    function assert(msg: boolean|ERROR.Message, f?: () => any[]) {
        // if a boolean (assume it is true, assuming usage above is obeyed)
        if (typeof (msg) === 'boolean' /* && msg */)
            return (f === undefined ? [] : f());

        // casts required due to dumb typescript...
        const error = new ErrorWrapper((<ERROR.Message>msg).message, 'Type Error', (<ERROR.Message>msg).ast);
        if (f === undefined)
            throw error;
        return [error].concat(f());
    };

    // typechecker error messages
    module ERROR {

        type AST_TYPE = AST.Exp.Exp | AST.Type.Type;

        export class Message {
            constructor(
                public message: string,
                public ast?: AST_TYPE) {
            }
        };

        export function UnknownType(id: string, ast: AST_TYPE) {
            return new Message('Unknown type ' + id, ast);
        };

        export function UnknownLocation(id: string, ast: AST_TYPE) {
            return new Message('Unknown location variable ' + id, ast);
        };

        export function UnexpectedResult(got: any, expected: any, ast: AST_TYPE) {
            return new Message('Unexpected result, got ' + got + ' expecting ' + expected, ast);
        };

        export function DuplicatedTypedef(id: string, ast: AST_TYPE) {
            return new Message('Duplicated typedef: ' + id, ast);
        };

        export function DuplicatedTag(id: string, ast: AST_TYPE) {
            return new Message('Duplicated tag: ' + id, ast);
        };

        export function InvalidSubstitution(t: Type, ast: AST_TYPE) {
            return new Message('Can only substitute a Type/LocationVariable, got:  ' + t.type, ast);
        };

        export function DuplicatedField(id: string, r: RecordType, ast: AST_TYPE) {
            return new Message('Duplicated field "' + id + '" in ' + r, ast);
        };

        export function ArgumentMismatch(got: number, expected: number, ast: AST_TYPE) {
            return new Message('Argument number mismatch, got: ' + got + ' expecting ' + expected, ast);
        };

        export function ExpectingLocation(i: number, t: Type, ast: AST_TYPE) {
            return new Message('Argument #' + i + ' must be a LocationVariable, got: ' + t.type, ast);
        };

        export function UnexpectedLocation(i: number, ast: AST_TYPE) {
            return new Message('Argument #' + i + ' cannot be a LocationVariable.', ast);
        };
    }

    //
    // AUX TYPEDEFS
    //

    type TypeEval = (c: EvalContext, env: Gamma) => Type;
    type ExpEval = (c: EvalContext, env: Gamma) => any[];

    interface EvalContext {
        checkExp(ast: AST.Exp.Exp, env: Gamma): any[];
        checkType(ast: AST.Type.Type, env: Gamma): Type;
    };

    type MatchType = AST.Type.MatchType<TypeEval>;
    type MatchExp = AST.Exp.MatchExp<ExpEval>;

    //
    // MATCH EXPRESSION
    //

    const matchExp: MatchExp = {

        Program: ast => (c, _) => {

            // ignores old environment, this is a new program!

            let typedef = new TypeDefinition();
            let env = new Gamma(typedef, null);

            // handle type definitions
            if (ast.typedefs !== null) {

                // 1st pass: extract all argument definitions, note that
                // duplication is not checked at this stage
                for (var i = 0; i < ast.typedefs.length; ++i) {
                    let it = ast.typedefs[i];
                    let args: (TypeVariable|LocationVariable)[] = [];
                    let pars = it.pars;

                    // only do this if there are any actual definition parameters
                    if (pars !== null) {
                        args = new Array(pars.length);

                        for (var j = 0; j < pars.length; ++j) {
                            // indexes MUST go [ n, n-1, ..., 1, 0 ] to match the
                            // desired depth of the DeBruijn indexes.
                            var n = pars[j];
                            args[j] = isTypeVariableName(n) ?
                                new TypeVariable(n, (pars.length - j - 1), null) :
                                new LocationVariable(n, (pars.length - j - 1));
                        }
                    }

                    assert(typedef.addType(it.id, args) || ERROR.DuplicatedTypedef(it.id, it));
                }

                // 2nd pass: check that any recursion is well-formed (i.e. correct number and kind of argument)
                for (var i = 0; i < ast.typedefs.length; ++i) {
                    var type = ast.typedefs[i];
                    var tmp_env = env;
                    var args: any = typedef.getType(type.id);

                    // sets the variables, if there are any to setup
                    if (args !== null) {
                        for (var j = 0; j < args.length; ++j) {
                            // should be for both LocationVariables and TypeVariables
                            tmp_env = tmp_env.newScope(args[j].name(), args[j], null);
                        }
                    }

                    // map of type names to typechecker types
                    // FIXME needs to ensure that definition is not a locationvariable?
                    assert(typedef.addDefinition(type.id, c.checkType(type.type, tmp_env))
                        || ERROR.DuplicatedTypedef(type.id, type));
                }

                /*
                // 3rd pass: check for bottom types.
                for (var i = 0; i < ast.typedefs.length; ++i) {
                    var type = ast.typedefs[i];
                    var x = typedef.getDefinition(type.id);
                    var set = new Set();
                    while (x.type === types.DefinitionType) {
                        // note that we use the string-indexOnly representation of the type
                        set.add(x.toString(false));
                        x = unfoldDefinition(x);
                        // if already seen this unfold, then type is a cycle
                        assert(!set.has(x.toString(false))
                            || ('Infinite typedef (i.e. bottom type): ' + type.id), type);
                    }
                } */

            }

            let tmp = [];
            // check main expressions:
            for (let exp of ast.exp) {
                tmp = tmp.concat(c.checkExp(exp, env));
            }

            return tmp;
        },

        Share: ast => (c, env) => {
            const cap = c.checkType(ast.type, env);
            const left = c.checkType(ast.a, env);
            const right = c.checkType(ast.b, env);

            // Protocol conformance, goes through all possible "protocol
            // interleaving" and ensures that all those possibilities are
            // considered in both protocols.

            const table = checkConformance(env, cap, left, right);
            const res = table !== null; // is valid if table not null
            // checkProtocolConformance(cap, left, right, ast);

            return assert(
                ast.value === res || ERROR.UnexpectedResult(res, ast.value, ast),
                () => [[ast, table]]
                );
        },

        // subtyping of types
        Subtype: ast => (c, env) => {
            const left = c.checkType(ast.a, env);
            const right = c.checkType(ast.b, env);
            const s = subtype(left, right);
            return assert(
                s == ast.value || ERROR.UnexpectedResult(s, ast.value, ast),
                () => []
                );
        },

        // equality of types
        Equals: ast => (c, env) => {
            const left = c.checkType(ast.a, env);
            const right = c.checkType(ast.b, env);
            const s = equals(left, right);

            return assert(
                s == ast.value || ERROR.UnexpectedResult(s, ast.value, ast),
                () => []
                );
        },

        Forall: ast => (c, env) => {
            let id = ast.id;
            let variable;
            let bound;

            if (isTypeVariableName(id)) {
                bound = !ast.bound ?
                    Top : // no bound, default is 'top'
                    // else check with empty environment (due to decidability issues)
                    c.checkType(ast.bound, new Gamma(env.getTypeDef(), null));
                variable = new TypeVariable(id, 0, bound);
            }
            else {
                variable = new LocationVariable(id, 0);
                bound = null;
            }

            let e = env.newScope(id, variable, bound);

            return c.checkExp(ast.exp, e)
        },
    };


    //
    // MATCH TYPE
    //

    const matchType: MatchType = {

        Substitution: ast => (c, env) => {
            const type = c.checkType(ast.type, env);
            const to = c.checkType(ast.to, env);
            const from = c.checkType(ast.from, env);

            assert((from.type === types.LocationVariable || from.type === types.TypeVariable)
                || ERROR.InvalidSubstitution(from, ast.from));

            // check above ensures that 'from' is either LocationVariable or TypeVariable.
            return substitution(type, <LocationVariable|TypeVariable>from, to);
        },

        // auxiliary function for common Forall/Exists code
        _aux_: (ctr, ast: AST.Type.Exists|AST.Type.Forall): TypeEval => (c, env) => {
            const id = ast.id;
            let variable: TypeVariable|LocationVariable;
            let bound: Type;

            if (isTypeVariableName(id)) {
                bound = !ast.bound ?
                    Top : // no bound, default is 'top'
                    // else check with empty environment (due to decidability issues)
                    c.checkType(ast.bound, new Gamma(env.getTypeDef(), null));
                variable = new TypeVariable(id, 0, bound);
            }
            else {
                variable = new LocationVariable(id, 0);
                bound = null;
            }

            const e = env.newScope(id, variable, bound);
            const type = c.checkType(ast.exp, e);

            return <Type>new ctr(variable, type, bound);
        },

        Exists: function(ast) { return this._aux_(ExistsType, ast); },
        Forall: function(ast) { return this._aux_(ForallType, ast); },

        Stacked: ast => (c, env) => {
            return new StackedType(
                c.checkType(ast.left, env),
                c.checkType(ast.right, env)
                );
        },

        Rely: ast => (c, env) => {
            const rely = c.checkType(ast.left, env);
            const guarantee = c.checkType(ast.right, env);
            return new RelyType(rely, guarantee);
        },

        Guarantee: ast => (c, env) => {
            const guarantee = c.checkType(ast.left, env);
            const rely = c.checkType(ast.right, env);
            return new GuaranteeType(guarantee, rely);
        },

        Sum: ast => (c, env) => {
            const sum = new SumType();
            for (let t of ast.sums) {
                assert(sum.add(t.tag, c.checkType(t.type, env)) ||
                    ERROR.DuplicatedTag(t.tag, t));
            }
            return sum;
        },

        Star: ast => (c, env) => {
            const star = new StarType();
            for (let t of ast.types) {
                star.add(c.checkType(t, env));
            }
            return star;
        },

        Alternative: ast => (c, env) => {
            const alt = new AlternativeType();
            for (let t of ast.types) {
                alt.add(c.checkType(t, env));
            }
            return alt;
        },

        Intersection: ast => (c, env) => {
            const alt = new IntersectionType();
            for (let t of ast.types) {
                alt.add(c.checkType(t, env));
            }
            return alt;
        },

        Function: ast => (c, env) => {
            return new FunctionType(
                c.checkType(ast.arg, env),
                c.checkType(ast.exp, env)
                );
        },

        Capability: ast => (c, env) => {
            let id = ast.id;
            let loc = env.getTypeByName(id);

            assert((loc !== undefined && loc.type === types.LocationVariable) ||
                ERROR.UnknownLocation(id, ast));

            return new CapabilityType((<LocationVariable>loc).copy(env.getNameIndex(id)), c.checkType(ast.type, env));
        },

        Name: ast => (c, env) => {
            // the typing environment remains unchanged because all type
            // definitions and type/location variables should not interfere
            const label = ast.text;
            const typedef = env.getTypeDef();
            const tmp = env.getTypeByName(label);
            // if label matches type in environment, but we only allow
            // access to type variables and location variables using this
            // AST.kind --- all other uses are assumed to be recursives.
            if (tmp !== undefined &&
                (tmp.type === types.TypeVariable ||
                    tmp.type === types.LocationVariable)) {
                return (<LocationVariable|TypeVariable>tmp).copy(env.getNameIndex(label));
            }

            // look for type definitions with 0 arguments
            var lookup_args = typedef.getType(label);
            if (lookup_args !== undefined && lookup_args.length === 0)
                return new DefinitionType(label, [], typedef);

            assert(ERROR.UnknownType(label, ast));
        },

        Reference: ast => (c, env) => {
            var id = ast.text;
            var loc = env.getTypeByName(id);

            assert((loc !== undefined && loc.type === types.LocationVariable) ||
                ERROR.UnknownLocation(id, ast));

            return new ReferenceType((<LocationVariable>loc).copy(env.getNameIndex(id)));
        },

        Bang: ast => (c, env) => {
            return new BangType(c.checkType(ast.type, env));
        },

        Record: ast => (c, env) => {
            var rec = new RecordType();
            for (var i = 0; i < ast.exp.length; ++i) {
                var field = ast.exp[i];
                var id = field.id;
                var value = c.checkType(field.exp, env);
                assert(rec.add(id, value) || ERROR.DuplicatedField(id, rec, field));
            }
            return rec;
        },

        Tuple: ast => (c, env): Type => {
            const rec = new TupleType();
            for (const exp of ast.exp) {
                rec.add(c.checkType(exp, env));
            }
            return rec;
        },

        Tagged: ast => (c, env): Type => {
            var sum = new SumType();
            var exp = c.checkType(ast.type, env);
            sum.add(ast.tag, exp);
            return sum;
        },

        Top: ast => (c, env) => {
            return Top;
        },

        Definition: ast => (c, env) => {
            var typedef = env.getTypeDef();
            var id = ast.name;
            var args = ast.args;
            var t_args = typedef.getType(id);

            assert(t_args !== undefined || ERROR.UnknownType(id, ast));
            assert(t_args.length === args.length || ERROR.ArgumentMismatch(args.length, t_args.length, ast));

            var arguments = new Array(args.length);
            for (var i = 0; i < args.length; ++i) {
                var tmp = c.checkType(args[i], env);

                if (t_args[i].type === types.LocationVariable) {
                    assert((tmp.type === types.LocationVariable) ||
                        ERROR.ExpectingLocation(i, tmp, args[i]));
                }

                if (t_args[i].type === types.TypeVariable) {
                    assert((tmp.type !== types.LocationVariable) ||
                        ERROR.UnexpectedLocation(i, args[i]));
                }

                arguments[i] = tmp;
            }

            return new DefinitionType(id, arguments, typedef);
        },

        Primitive: ast => (c, env) => {
            // relying on the parser to limit primitive types to ints, etc.
            return new PrimitiveType(ast.text);
        },

        None: ast => (c, env) => {
            // uses singleton NoneType, there is only one.
            return None;
        },
    };

    // only exports checking function.
    export function checker(ast: AST.Exp.Program): { time: number, info: any[] } {

        const log = { 
            // timer start
            time: (new Date().getTime()),
            // info place_holder
            info: []
        };

        const c: EvalContext = {

            // for expressions
            checkExp: function(ast: AST.Exp.Exp, env: Gamma) {
                return (ast.match(matchExp))(c, env);
            },

            // for types
            checkType: function(ast: AST.Type.Type, env: Gamma) {
                return (ast.match(matchType))(c, env);
            },
        };

        try {
            log.info = c.checkExp(ast, null);
            return log;
        } finally {
            // because exceptions may be thrown
            log.time = (new Date().getTime()) - log.time;
        }

    };

};
