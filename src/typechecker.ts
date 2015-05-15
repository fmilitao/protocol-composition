// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

module TypeChecker {

    const Unit = new BangType(new RecordType());
    const None = new NoneType();
    const Top = new TopType();

    /**
     * Use as:
     *        assert( BOOLEAN_CONDITION || ERROR_MSG( STRING, AST ) );
     * so as to only compute ERROR_MSG if BOOLEAN_CONDITION is false.
     */
    function assert(msg: boolean|ERROR.Message, f? : ()=>any[] ) {
        // if a boolean and true
        if (typeof (msg) === 'boolean' && msg)
            return (f===undefined ? [] : f());
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
    // Auxiliary Definitions
    //

    // TypeVariables must start upper cased.
    function isTypeVariableName(n: string) {
        return n[0] === n[0].toUpperCase();
    };

    var unifyRely = function(id, step, state) {
        switch (step.type) {
            case types.ExistsType: id
                return unifyRely( // must shift indexes to match new depth
                    shift(id, 0, 1),
                    step.inner(),
                    shift(state, 0, 1));
            case types.RelyType:
                return unify(id, step.rely(), state);
            case types.AlternativeType: {
                var is = step.inner();
                for (var i = 0; i < is.length; ++i) {
                    var tmp = unifyRely(id, is[i], state);
                    // if found one unification that is valid (either empty or not)
                    if (tmp !== false)
                        return tmp;
                }
                return false;
            }
            case types.IntersectionType: {
                var is = step.inner();
                var res = null; // assuming at least one element in 'is'
                for (var i = 0; i < is.length; ++i) {
                    var tmp = unifyRely(id, is[i], state);
                    // if one fails, they all do.
                    if (tmp === false)
                        return tmp;
                    if (res === null) {
                        res = tmp;
                    } else {
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

    var unifyGuarantee = function(id, step, state) {
        switch (step.type) {
            case types.ForallType:
                return unifyGuarantee(shift(id, 0, 1), step.inner(), shift(state, 0, 1));
            case types.GuaranteeType:
                return unify(id, step.guarantee(), state);
            case types.AlternativeType: {
                var is = step.inner();
                for (var i = 0; i < is.length; ++i) {
                    var tmp = unifyGuarantee(id, is[i], state);
                    // if found one unification that is valid (either empty or not)
                    if (tmp !== false)
                        return tmp;
                }
                return false;
            }
            case types.IntersectionType: {
                var is = step.inner();
                var res = null; // assuming at least one element in 'is'
                for (var i = 0; i < is.length; ++i) {
                    var tmp = unifyGuarantee(id, is[i], state);
                    // if one fails, they all do.
                    if (tmp === false)
                        return tmp;
                    if (res === null) {
                        res = tmp;
                    } else {
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

    var contains = function(visited, w) {
        for (var v of visited) {
            // must assume that all types were normalized to have their
            // indexes compacted in order to ensure termination.
            // Therefore, we do not need to check gamma.
            // by (rs:Weakening) and by (rs:Subsumption)
            if (subtype(w.s, v.s) &&
                subtype(v.p, w.p) &&
                subtype(v.q, w.q))
                return true;
        }

        return false;
    };

    //
    // Protocol Conformance
    //

    var Work = function(s, p, q) {
        return { s: s, p: p, q: q };
    };

    var checkConformance = function(g, s, p, q) {
        // we can ignore 'g' because of using indexes
        var work = [Work(s, p, q)];
        var visited = [];
        return checkConformanceAux(work, visited);
    };

    var checkConformanceAux = function(work, visited) {

        // var i=0;
        // console.debug( '' );
        while (work.length > 0) {
            var w = work.pop();

            if (!contains(visited, w)) {
                var s = w.s;
                var p = w.p;
                var q = w.q;

                // console.debug( (i++)+' : '+s+' >> '+p+' || '+q );
                var left = step(s, p, q, true);
                var right = step(s, q, p, false);
                if (left === null || right === null)
                    return null; // fails

                work = work.concat(left).concat(right);

                visited.push(w);
            }

            // if( i > 100 ) //FIXME this is temporary.
            //  error('loop bug...');
        }
        return visited;
    }

    var step = function(s, p, q, isLeft) {
        // expands recursion
        s = unfold(s);
        p = unfold(p);

        var res = singleStep(s, p, q, isLeft);
        if (res !== null)
            return res; // valid stepping

        // else step failed, attempt breaking 's' or 'p'

        // by (rs:StateAlternative)
        if (s.type === types.AlternativeType) {
            var ss = s.inner();
            var res: any = [];
            // protocol must consider *all* cases
            for (var i = 0; i < ss.length; ++i) {
                var tmp = step(ss[i], p, q, isLeft);
                // one failed!
                if (tmp === null) {
                    res = null; // signal fail
                    break;
                }
                res = res.concat(tmp);
            }

            if (res !== null)
                return res;
            // else intentionally fall through
        }

        // by (rs:ProtocolIntersection)
        if (p.type === types.IntersectionType) {
            var pp = p.inner();
            var res: any = [];
            // protocol must consider *all* cases
            for (var i = 0; i < pp.length; ++i) {
                var tmp = step(s, pp[i], q, isLeft);
                // one failed!
                if (tmp === null) {
                    res = null;
                    break;
                }
                res = res.concat(tmp);
            }
            if (res !== null)
                return res;
            // else intentionally fall through
        }

        // by (rs:ProtocolAlternative)
        if (p.type === types.AlternativeType) {
            var pp = p.inner();
            // protocol only needs to consider *one* case
            for (var i = 0; i < pp.length; ++i) {
                var tmp = step(s, pp[i], q, isLeft);
                // one steps, we are done
                if (tmp !== null)
                    return tmp;
            }

            // did not find a good step, fall through.
        }

        // by (rs:StateIntersection)
        if (s.type === types.IntersectionType) {
            var ss = s.inner();
            // protocol only needs to consider *one* case
            for (var i = 0; i < ss.length; ++i) {
                var tmp = step(ss[i], p, q, isLeft);
                // one steps, we are done
                if (tmp !== null)
                    return tmp;
            }

            // did not find a good step, fall through.
        }

        // fails to step
        return null;
    };

    // may return null on failed stepping, or set of new configurations
    var singleStep = function(s, p, q, isLeft) {

        var R = function(s, p) {
            var tmp = reIndex(s, p, q);
            s = tmp[0];
            p = tmp[1];
            q = tmp[2];

            return isLeft ? Work(s, p, q) : Work(s, q, p);
        };

        // by (rs:None)
        if (p.type === types.NoneType) {
            // no need to add new work, we already know this configuration steps
            return [];
        }

        if (isProtocol(s)) {
            // PROTOCOL STEPPING

            // by (ps:ExistsType) and by (ps:ExistsLoc)
            if (s.type === types.ExistsType && p.type === types.ExistsType) {

                if (s.id().type !== p.id().type)
                    return null; // type mismatch
                //TODO: also check bound

                // must shift index in 'q' to match depth of the opened existential
                return step(s.inner(), p.inner(), shift(q, 0, 1), isLeft);
            }

            // by (ps:ForallType) and by (ps:ForallLoc)
            if (s.type === types.RelyType && s.guarantee().type === types.ForallType &&
                p.type === types.RelyType && p.guarantee().type === types.ForallType) {

                // check 's' and 'p' guarantee: ( G ; R )
                var gs = s.guarantee();
                var gp = p.guarantee();

                if (gs.id().type !== gp.id().type)
                    return null;
                //TODO: also check bound

                s = new RelyType(shift(s.rely(), 0, 1), gs.inner());
                p = new RelyType(shift(p.rely(), 0, 1), gs.inner());
                q = shift(q, 0, 1); // must match same depth as others

                return step(s, p, q, isLeft);
            }

            // by (ps:TypeApp) and by (ps:LocApp)
            if (s.type === types.RelyType && s.guarantee().type === types.ForallType &&
                p.type === types.RelyType && p.guarantee().type !== types.ForallType) {
                // unifies the guarantee of 's' with that of 'p'
                var b = s.guarantee();
                var i = b.id();
                var t = b.inner();

                // find the guarantee:
                b = p.guarantee();
                if (b.type === types.GuaranteeType)
                    b = b.guarantee();
                // else the next step was omitted.

                // shifts 'b' to the same depth as 't'
                var x = unifyGuarantee(i, t, shift(b, 0, 1));

                // fails to unify
                if (x === false)
                    return null;
                // TODO: check bound
                // is some valid unification
                if (x !== true) {
                    t = substitution(t, i, x);
                }
                // unshift because we are opening the forall
                t = shift(t, 0, -1);

                return step(new RelyType(s.rely(), t), p, q, isLeft);
            }

            // by (ps:Step)
            if (s.type === types.RelyType && p.type === types.RelyType && subtype(s.rely(), p.rely())) {
                // check 's' and 'p' guarantee: ( G ; R )
                var gs = s.guarantee();
                var gp = p.guarantee();

                // account for omitted guarantees (i.e.: 'G' == 'G ; none')
                if (gs.type !== types.GuaranteeType) {
                    gs = new GuaranteeType(gs, None);
                }
                if (gp.type !== types.GuaranteeType) {
                    gp = new GuaranteeType(gp, None);
                }

                // guarantee state must match
                if (subtype(gp.guarantee(), gs.guarantee())) {
                    return [R(gs.rely(), gp.rely())];
                }
            }

            return null;

        } else {
            // STATE STEPPING

            // by (ss:Recovery)
            if (equals(s, p)) {
                return [R(None, None)];
            }

            // by (ss:OpenType) and by (ss:OpenLoc)
            if (p.type === types.ExistsType) {
                // attempts to find matching type/location to open existential
                // correctness of type bound is checked inside 'unifyExists'
                var i = p.id();
                var t = p.inner();
                // shifts 's' to the same depth as 't'
                var x = unifyRely(i, t, shift(s, 0, 1));

                // fails to unify
                if (x === false)
                    return null;
                // TODO: check bound
                // is some valid unification
                if (x !== true) {
                    t = substitution(t, i, x);
                }
                // unshift because we are opening the existential
                t = shift(t, 0, -1);

                return step(s, t, q, isLeft);
            }

            // by (ss:ForallType) and by (ss:ForallLoc)
            if (p.type === types.RelyType && p.guarantee().type === types.ForallType) {

                // opening the forall, we must ensure that all old indexes match the new depth
                p = new RelyType(
                    shift(p.rely(), 0, 1),
                    p.guarantee().inner() // direct access to forall guarantee
                    );
                q = shift(q, 0, 1);
                s = shift(s, 0, 1);

                return step(s, p, q, isLeft);
            }

            // by (ss:Step)
            if (p.type === types.RelyType && subtype(s, p.rely())) {
                var b = p.guarantee();
                if (b.type === types.GuaranteeType) {
                    // single step of the protocol
                    return [R(b.guarantee(), b.rely())];
                } else {
                    // assume case is that of omitted '; none' and that 'b' is the new state.
                    // assume that type was previously checked to be well-formed.
                    return [R(b, None)];
                }
            }

            return null;
        }
    };

    var reIndex = function(s, a, b) {
        var set = indexSet(s);
        indexSet(a).forEach(function(v) { set.add(v); });
        indexSet(b).forEach(function(v) { set.add(v); });

        if (set.size > 0) {
            var v = [];
            set.forEach(function(val) { v.push(val); });
            v.sort();
            // find shifting value
            for (var i = 0; i < v.length; ++i) {
                if (v[i] !== i) {
                    v[i] = i - v[i] - (i > 0 ? v[i - 1] : 0);
                } else {
                    v[i] = 0; // no shift
                }
            }
            // apply shifts
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

    //
    // TYPES
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
                    let args: Type[] = [];
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

            return substitution(type, from, to);
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
