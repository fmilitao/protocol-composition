// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

module TypeChecker {

    //
    // Auxiliary Definitions
    //

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

    export function checkConformance(g, s, p, q) {
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

};
