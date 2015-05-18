// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
var TypeChecker;
(function (TypeChecker) {
    function isProtocol(t, trail) {
        if (t instanceof TypeChecker.NoneType || t instanceof TypeChecker.RelyType)
            return true;
        if (t instanceof TypeChecker.ExistsType)
            return isProtocol(t.inner(), trail);
        if (t instanceof TypeChecker.AlternativeType || t instanceof TypeChecker.IntersectionType || t instanceof TypeChecker.StarType) {
            for (var _i = 0, _a = t.inner(); _i < _a.length; _i++) {
                var p = _a[_i];
                if (!isProtocol(p, trail))
                    return false;
            }
            return true;
        }
        if (t instanceof TypeChecker.DefinitionType) {
            if (trail === undefined) {
                trail = new Set();
            }
            var key = t.toString(true);
            if (trail.has(key))
                return true;
            trail.add(key);
            return isProtocol(TypeChecker.unfold(t), trail);
        }
        return false;
    }
    ;
    function unifyRely(id, step, state) {
        if (step instanceof TypeChecker.ExistsType) {
            return unifyRely(TypeChecker.shift(id, 0, 1), step.inner(), TypeChecker.shift(state, 0, 1));
        }
        if (step instanceof TypeChecker.RelyType) {
            return TypeChecker.unify(id, step.rely(), state);
        }
        if (step instanceof TypeChecker.AlternativeType) {
            for (var _i = 0, _a = step.inner(); _i < _a.length; _i++) {
                var is = _a[_i];
                var tmp = unifyRely(id, is, state);
                if (tmp !== false)
                    return tmp;
            }
            return false;
        }
        if (step instanceof TypeChecker.IntersectionType) {
            var res = null;
            for (var _b = 0, _c = step.inner(); _b < _c.length; _b++) {
                var is = _c[_b];
                var tmp = unifyRely(id, is, state);
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
        return false;
    }
    ;
    function unifyGuarantee(id, step, state) {
        if (step instanceof TypeChecker.ForallType) {
            return unifyGuarantee(TypeChecker.shift(id, 0, 1), step.inner(), TypeChecker.shift(state, 0, 1));
        }
        if (step instanceof TypeChecker.GuaranteeType)
            return TypeChecker.unify(id, step.guarantee(), state);
        if (step instanceof TypeChecker.AlternativeType) {
            for (var _i = 0, _a = step.inner(); _i < _a.length; _i++) {
                var is = _a[_i];
                var tmp = unifyGuarantee(id, is, state);
                if (tmp !== false)
                    return tmp;
            }
            return false;
        }
        if (step instanceof TypeChecker.IntersectionType) {
            var res = null;
            for (var _b = 0, _c = step.inner(); _b < _c.length; _b++) {
                var is = _c[_b];
                var tmp = unifyGuarantee(id, is, state);
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
        return false;
    }
    ;
    function contains(visited, w) {
        for (var _i = 0; _i < visited.length; _i++) {
            var v = visited[_i];
            if (TypeChecker.subtype(w.s, v.s) &&
                TypeChecker.subtype(v.p, w.p) &&
                TypeChecker.subtype(v.q, w.q))
                return true;
        }
        return false;
    }
    ;
    function Work(s, p, q) {
        return { s: s, p: p, q: q };
    }
    ;
    function checkConformance(g, s, p, q) {
        return checkConformanceAux([Work(s, p, q)], []);
    }
    TypeChecker.checkConformance = checkConformance;
    ;
    function checkConformanceAux(work, visited) {
        while (work.length > 0) {
            var w = work.pop();
            if (!contains(visited, w)) {
                var left = step(w.s, w.p, w.q, true);
                var right = step(w.s, w.q, w.p, false);
                if (left === null || right === null)
                    return null;
                work = work.concat(left).concat(right);
                visited.push(w);
            }
        }
        return visited;
    }
    function step(s, p, q, isLeft) {
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
    }
    ;
    function singleStep(s, p, q, isLeft) {
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
        if (isProtocol(s)) {
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
                    gs = new TypeChecker.GuaranteeType(gs, TypeChecker.None);
                }
                if (gp.type !== TypeChecker.types.GuaranteeType) {
                    gp = new TypeChecker.GuaranteeType(gp, TypeChecker.None);
                }
                if (TypeChecker.subtype(gp.guarantee(), gs.guarantee())) {
                    return [R(gs.rely(), gp.rely())];
                }
            }
            return null;
        }
        else {
            if (TypeChecker.equals(s, p)) {
                return [R(TypeChecker.None, TypeChecker.None)];
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
                    return [R(b, TypeChecker.None)];
                }
            }
            return null;
        }
    }
    ;
    function reIndex(s, a, b) {
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
    }
    ;
})(TypeChecker || (TypeChecker = {}));
;
