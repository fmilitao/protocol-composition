// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/**
 * INCLUDE parser.js
 * INCLUDE typechecker.types.js
 * INCLUDE typechecker.utils.js
 * 	AST : AST.kinds, for all AST case analysis needs.
 *  TypeChecker : stuff in typechecker.*.js
 */

module TypeChecker {

    // define constants for convenience
    // const assert = exports.assert;
    // const error = exports.error;
    //
    // const types = exports.types;
    // const fct = exports.factory;

    const FunctionType = fct.FunctionType;
    const BangType = fct.BangType;
    const SumType = fct.SumType;
    const StarType = fct.StarType;
    const AlternativeType = fct.AlternativeType;
    const IntersectionType = fct.IntersectionType;
    const ForallType = fct.ForallType;
    const ExistsType = fct.ExistsType;
    const RecordType = fct.RecordType;
    const TupleType = fct.TupleType;
    const ReferenceType = fct.ReferenceType;
    const StackedType = fct.StackedType;
    const CapabilityType = fct.CapabilityType;
    const LocationVariable = fct.LocationVariable;
    const TypeVariable = fct.TypeVariable;
    const PrimitiveType = fct.PrimitiveType;
    const RelyType = fct.RelyType;
    const DefinitionType = fct.DefinitionType;
    const GuaranteeType = fct.GuaranteeType;

    const UnitType = new BangType(new RecordType());
    const NoneType = new fct.NoneType();
    const TopType = new fct.TopType();

    // const Gamma = exports.Gamma;
    // const TypeDefinition = exports.TypeDefinition;
    //
    // const shift = exports.shift;
    // const unify = exports.unify;
    // const unfold = exports.unfold;
    // const unfoldDefinition = exports.unfoldDefinition;
    // const substitution = exports.substitution;
    // const subtype = exports.subtype;
    // const equals = exports.equals;
    // const isFree = exports.isFree;
    // const isProtocol = exports.isProtocol;
    // const indexSet = exports.indexSet;

    //
    // Auxiliary Definitions
    //

    // TypeVariables must start upper cased.
    var isTypeVariableName = function(n) {
        return n[0] === n[0].toUpperCase();
    }

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
            // 	error('loop bug...');
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
                    gs = new GuaranteeType(gs, NoneType);
                }
                if (gp.type !== types.GuaranteeType) {
                    gp = new GuaranteeType(gp, NoneType);
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
                return [R(NoneType, NoneType)];
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
                    return [R(b, NoneType)];
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


				const matchExp = {

        // TypeDef should not be used at this level
        TypeDef: x => assert(false, x),

        Program: ast => (c, _) => {

            // ignores old environment, this is a new program!

            let typedef = new TypeDefinition();
            let env = new Gamma(typedef, null);

            // handle type definitions
            if (ast.typedefs !== null) {

                // 1st pass: extract all argument definitions, note that
                // duplication is not checked at this stage
                for (var i = 0; i < ast.typedefs.length; ++i) {
                    var it = ast.typedefs[i];
                    var args: any = [];
                    var pars = it.pars;

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

                    assert(typedef.addType(it.id, args)
                        || ('Duplicated typedef: ' + it.id), it);
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
                        || ('Duplicated typedef: ' + type.id), type);
                }

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

                }

            }

            // check main expressions:
            for (let exp of ast.exp) {
                c.checkExp(exp, env);
            }

            // FIXME: bogus return...
            return NoneType;
        },

        Share: ast => (c, env) => {
            var cap = c.checkType(ast.type, env);
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);

            // Protocol conformance, goes through all possible "protocol
            // interleaving" and ensures that all those possibilities are
            // considered in both protocols.

            var table = checkConformance(env, cap, left, right);
            var res = table !== null; // is valid if table not null
            // checkProtocolConformance(cap, left, right, ast);

            assert(ast.value === res || ('Unexpected Result, got ' + res + ' expecting ' + ast.value), ast);

            //FIXME return type should depend on the kind of node: types -> type , construct -> some info.
            // returns an array or null
            return table;
        },

        // subtyping of types
        Subtype: ast => (c, env) => {
            var left = c.checkType(ast.a, env);
            var right = c.checkType(ast.b, env);
            var s = subtype(left, right);
            assert(s == ast.value || ('Unexpected Result, got ' + s + ' expecting ' + ast.value), ast);
            return left;
        },

								// equality of types
								Equals: ast => (c, env) => {
            let left = c.checkType(ast.a, env);
            let right = c.checkType(ast.b, env);
            let s = equals(left, right);
            assert(s == ast.value || ('Unexpected Result, got ' + s + ' expecting ' + ast.value), ast);
            return left;
        },

								Forall: ast => (c, env) => {
            let id = ast.id;
            let variable;
            let bound;

            if (isTypeVariableName(id)) {
                bound = !ast.bound ?
                    TopType : // no bound, default is 'top'
                    // else check with empty environment (due to decidability issues)
                    c.checkType(ast.bound, new Gamma(env.getTypeDef(), null));
                variable = new TypeVariable(id, 0, bound);
            }
            else {
                variable = new LocationVariable(id, 0);
                bound = null;
            }

            let e = env.newScope(id, variable, bound);
            let type = c.checkExp(ast.exp, e);

            return new ForallType(variable, type, bound);
        },
				};

				const matchType = {

        Substitution: ast => (c, env) => {
            const type = c.checkType(ast.type, env);
            const to = c.checkType(ast.to, env);
            const from = c.checkType(ast.from, env);

            assert((from.type === types.LocationVariable || from.type === types.TypeVariable)
                || ("Can only substitute a Type/LocationVariable, got: " + from.type), ast.from);

            return substitution(type, from, to);
        },

        // auxiliary function for common Forall/Exists code
        _aux_: (ctr, ast: AST.Type.Exists|AST.Type.Forall) => (c, env) => {
            var id = ast.id;
            var variable;
            var bound;

            if (isTypeVariableName(id)) {
                bound = !ast.bound ?
                    TopType : // no bound, default is 'top'
                    // else check with empty environment (due to decidability issues)
                    c.checkType(ast.bound, new Gamma(env.getTypeDef(), null));
                variable = new TypeVariable(id, 0, bound);
            }
            else {
                variable = new LocationVariable(id, 0);
                bound = null;
            }

            var e = env.newScope(id, variable, bound);
            var type = c.checkType(ast.exp, e);

            return new ctr(variable, type, bound);
        },

        Exists: ast => matchType._aux_(ExistsType, ast),
        Forall: ast => matchType._aux_(ForallType, ast),

        Stacked: ast => (c, env) => {
            return new StackedType(
                c.checkType(ast.left, env),
                c.checkType(ast.right, env)
                );
        },

        Rely: ast => (c, env) => {
            var rely = c.checkType(ast.left, env);
            var guarantee = c.checkType(ast.right, env);
            return new RelyType(rely, guarantee);
        },

        Guarantee: ast => (c, env) => {
            var guarantee = c.checkType(ast.left, env);
            var rely = c.checkType(ast.right, env);
            return new GuaranteeType(guarantee, rely);
        },

        Sum: ast => (c, env) => {
            const sum = new SumType();
            for (var i = 0; i < ast.sums.length; ++i) {
                const tag = ast.sums[i].tag;
                assert(sum.add(tag, c.checkType(ast.sums[i].exp, env)) ||
                    "Duplicated tag: " + tag, ast.sums[i]);
            }
            return sum;
        },

        Star: ast => (c, env) => {
            const star = new StarType();
            for (var i = 0; i < ast.types.length; ++i) {
                star.add(c.checkType(ast.types[i], env));
            }
            return star;
        },

        Alternative: ast => (c, env) => {
            const alt = new AlternativeType();
            for (var i = 0; i < ast.types.length; ++i) {
                alt.add(c.checkType(ast.types[i], env));
            }
            return alt;
        },

        Intersection: ast => (c, env) => {
            const alt = new IntersectionType();
            for (var i = 0; i < ast.types.length; ++i) {
                alt.add(c.checkType(ast.types[i], env));
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
            var id = ast.id;
            var loc = env.getTypeByName(id);

            assert((loc !== undefined && loc.type === types.LocationVariable) ||
                ('Unknow Location Variable ' + id), ast);

            return new CapabilityType(loc.copy(env.getNameIndex(id)), c.checkType(ast.type, env));
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
                return tmp.copy(env.getNameIndex(label));
            }

            // look for type definitions with 0 arguments
            var lookup_args = typedef.getType(label);
            if (lookup_args !== undefined && lookup_args.length === 0)
                return new DefinitionType(label, [], typedef);

            assert('Unknown type ' + label, ast);
        },

        Reference: ast => (c, env) => {
            var id = ast.text;
            var loc = env.getTypeByName(id);

            assert((loc !== undefined && loc.type === types.LocationVariable) ||
                ('Unknow Location Variable ' + id), ast);

            return new ReferenceType(loc.copy(env.getNameIndex(id)));
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
                assert(rec.add(id, value) ||
                    ("Duplicated field '" + id + "' in '" + rec + "'"), field);
            }
            return rec;
        },

        // should never occur at top level
        Field: ast => assert(false, ast),

        Tuple: ast => (c, env) => {
            // Note that TUPLE cannot move to the auto-bang block
            // because it may contain pure values that are not in the
            // typing environment and therefore, its type is only bang
            // or not as a consequence of each field's type and not just
            // what it consumes from the environment
            var rec = new TupleType();
            var bang = true;

            for (var i = 0; i < ast.exp.length; ++i) {
                var value = c.checkType(ast.exp[i], env);
                rec.add(value);
                if (value.type !== types.BangType)
                    bang = false;
            }

            if (bang)
                rec = new BangType(rec);

            return rec;
        },

        Tagged: ast => (c, env) => {
            var sum = new SumType();
            var tag = ast.tag;
            var exp = c.checkType(ast.exp, env);
            sum.add(tag, exp);
            if (exp.type === types.BangType) {
                sum = new BangType(sum);
            }
            return sum;
        },

        Top: ast => (c, env) => {
            return TopType;
        },


        Definition: ast => (c, env) => {
            var typedef = env.getTypeDef();
            var id = ast.name;
            var args = ast.args;
            var t_args = typedef.getType(id);

            assert(t_args !== undefined || ('Unknown typedef: ' + id), ast);
            assert(t_args.length === args.length ||
                ('Argument number mismatch: ' + args.length + ' vs ' + t_args.length), ast);

            var arguments = new Array(args.length);
            for (var i = 0; i < args.length; ++i) {
                var tmp = c.checkType(args[i], env);

                if (t_args[i].type === types.LocationVariable) {
                    assert((tmp.type === types.LocationVariable) ||
                        ('Argument #' + i + ' is not LocationVariable: ' + tmp.type),
                        args[i]);
                }

                if (t_args[i].type === types.TypeVariable) {
                    assert((tmp.type !== types.LocationVariable) ||
                        ('Argument #' + i + ' cannot be a LocationVariable'),
                        args[i]);
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
												return NoneType;
								},
				};

    /*
    // inspector( ast, env, checkFunction )
    var buildChecker = function(inspector) {
        var map: any = new Map();
        var aux = function(ast, env) {
            if (!map.has(ast.kind))
                error('Error @buildChecker Not expecting ' + ast.kind);
            return map.get(ast.kind)(ast, env);
        };

        var tmp = aux;
        if (inspector) {
            tmp = function(ast, env) {
                return inspector(ast, env, aux);
            };
        }

        for (var i in AST) {
            error(!map.has(i) || ('Error @buildChecker, duplication: ' + i));
            // find function to call on this kind of AST node
            map.set(i, setupAST(i, tmp));
        }

        return tmp;
    };

    // this moved here just to avoid re building checker on each 'check'
    // all these variable could be local variables of 'exports.check'
    var type_info = [];
    var inspector = function(ast, env, c) {
        var info: any = { ast: ast, env: env };
        type_info.push(info);

        var res = c(ast, env);
        info.res = res;

        // this is a very hackish way to extract conformance table without
        // breaking the inner return type signature!
        if (ast.kind === AST.SHARE) {
            // unit
            return UnitType;
        }

        return res;
    };
    var checker = buildChecker(inspector);
    */

    // only exports checking function.
    export function checker(ast: AST.Exp.Program, log) : any {

        //type_info = []; // reset

        // timer start
        let start = new Date().getTime();
        let c = {

            // for expressions
            checkExp: (ast: AST.Exp.Exp, env) => {
                return (ast.match<any>(matchExp))(c, env);
            },

            // for types
            checkType: (ast: AST.Type.Type, env) => {
                return (ast.match<any>(matchType))(c, env);
            },
        };

        try {
            return c.checkExp(ast, c);
        } finally {
            if (log) {
                log.diff = (new Date().getTime()) - start;
                //log.info = type_info;
            }
        }

    };

    //return exports;

};



	// well-formed checks are currently work-in-progress.

	/*
	var locSet = function( t ){

		if( isProtocol(t) )
			return new Set(); // empty set

		switch( t.type ){
			case types.NoneType:
				return new Set(); // empty set

			case types.RelyType:
				return locSet( t.rely() );

			case types.GuaranteeType:
				return locSet( t.guarantee() );

			case types.AlternativeType:
			case types.IntersectionType:
			case types.StarType: {
				var ts = t.inner();
				var tmp = new Set();

				for( var i=0; i<ts.length; ++i ){
					locSet( ts[i] ).forEach(
						function(x){
							tmp.add(x);
						});
				}

				return tmp;
			}

			case types.ExistsType:
			case types.ForallType:{
				var tmp = locSet( t.inner() )
				var id = t.id().name();

				if( !isTypeVariableName( id ) ){
					// then is location variable
					// and we must remove it, if present, from the set

					tmp.delete( id );
				}

				return tmp;
			}

			case types.CapabilityType:
				return locSet( t.location() );

			case types.LocationVariable:
				return new Set( [t.name()]) ;

			case types.DefinitionType:
				return locSet( unfold(t) );

			default:
				error( '@locSet: invalid type, got: '+t.type+' '+t );
		}
	}
	*/

	/*
	var wfProtocol = function( t ){
		if( !isProtocol(t) )
			return false;

		switch( t.type ){
			case types.NoneType:
				return true; // empty set

			case types.RelyType: {
				var r = locSet( t.rely() );
				var g = locSet( t.guarantee() );

				if( r.size !== g.size )
					return false;

				var tmp = true;
				r.forEach(function(v){
					if( !g.has(v) )
						tmp = false;
				});
				// some missing element
				if( !tmp )
					return false;

				return true;
			}

			case types.GuaranteeType:
				return wfProtocol( t.guarantee() ) && wfProtocol( t.rely() );

			case types.AlternativeType: {
				// needs to check there is a different rely
				// all must be valid protocols
				// how to express this with existentials?
				// this check should be in the step, not here.
				return true;
			}

			case types.IntersectionType: {
				// all must be valid protocols
				var ts = t.inner();

				for( var i=0; i<ts.length; ++i ){
					if( !wfProtocol( ts[i] ) )
						return false;
				}

				return true;
			}

			case types.StarType:
			case types.ExistsType:
			case types.ForallType:{
				// needs to consider: P * exists q.(A), etc.
				return true;
			}

			case types.DefinitionType:
				return wfProtocol( unfold(t) );

			default:
				error( '@wfProtocol: invalid type, got: '+t.type );
		}
		return true;
	}
	*/
