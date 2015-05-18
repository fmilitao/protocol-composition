// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
var TypeChecker;
(function (TypeChecker) {
    function unify(x, t, a) {
        if (x.type !== TypeChecker.types.LocationVariable &&
            x.type !== TypeChecker.types.TypeVariable) {
            TypeChecker.error("@unify: can only unify a Type/LocationVariable, got: " + x.type);
        }
        return unifyAux(x, t, a, new Set());
    }
    TypeChecker.unify = unify;
    ;
    function unifyAux(x, t, a, trail) {
        if (x.type === t.type && x.index() === t.index() && ((x.type === TypeChecker.types.LocationVariable && a.type === TypeChecker.types.LocationVariable) ||
            (x.type === TypeChecker.types.TypeVariable && a.type !== TypeChecker.types.LocationVariable)))
            return a;
        var deft = t.type === TypeChecker.types.DefinitionType;
        var defa = a.type === TypeChecker.types.DefinitionType;
        if (deft || defa) {
            var key = t.toString(true) + a.toString(true);
            if (trail.has(key))
                return true;
            trail.add(key);
            t = deft ? unfold(t) : t;
            a = defa ? unfold(a) : a;
            return unifyAux(x, t, a, trail);
        }
        if (t.type !== a.type)
            return false;
        var tmp = true;
        var aux = function (value) {
            if (tmp === false || value === false) {
                tmp = false;
                return false;
            }
            if (tmp === true) {
                tmp = value;
                return true;
            }
            if (value === true)
                return true;
            return equals(tmp, value);
        };
        switch (t.type) {
            case TypeChecker.types.FunctionType: {
                if (!aux(unifyAux(x, t.argument(), a.argument(), trail)) ||
                    !aux(unifyAux(x, t.body(), a.body(), trail)))
                    return false;
                return tmp;
            }
            case TypeChecker.types.BangType:
                return unifyAux(x, t.inner(), a.inner(), trail);
            case TypeChecker.types.RelyType:
            case TypeChecker.types.GuaranteeType: {
                if (!aux(unifyAux(x, t.rely(), a.rely(), trail)) ||
                    !aux(unifyAux(x, t.guarantee(), a.guarantee(), trail)))
                    return false;
                return tmp;
            }
            case TypeChecker.types.SumType: {
                var ts_1 = t.tags();
                var as_1 = a.tags();
                if (ts_1.length !== as_1.length)
                    return false;
                for (var i in ts_1) {
                    var tt = t.inner(ts_1[i]);
                    var at = a.inner(ts_1[i]);
                    if (at === undefined || !aux(unifyAux(x, tt, at, trail)))
                        return false;
                }
                return tmp;
            }
            case TypeChecker.types.AlternativeType:
            case TypeChecker.types.IntersectionType:
            case TypeChecker.types.StarType: {
                var ts = t.inner();
                var as = a.inner();
                if (ts.length > as.length)
                    return false;
                var tt = null;
                var tcount = 0;
                var as = as.slice(0);
                for (var i = 0; i < ts.length; ++i) {
                    var found = false;
                    for (var j = 0; j < as.length; ++j) {
                        if (equals(ts[i], as[j])) {
                            as.splice(j, 1);
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        if (tt !== null && !equals(tt, ts[i])) {
                            return false;
                        }
                        tt = ts[i];
                        tcount += 1;
                    }
                }
                if (as.length === 0) {
                    return true;
                }
                if (tt === null || tcount === 0) {
                    return false;
                }
                if (tcount > 1) {
                    if (as.length % tcount !== 0)
                        return false;
                    var cs = new Array(as.length);
                    for (var i = 0; i < as.length; ++i) {
                        cs[i] = 1;
                        for (var j = i + 1; j < as.length; ++j) {
                            if (equals(as[i], as[j])) {
                                cs[i] += 1;
                                as.splice(j, 1);
                                --j;
                            }
                        }
                    }
                    for (var i = 0; i < as.length; ++i) {
                        if (cs[i] % tcount !== 0)
                            return false;
                    }
                }
                var tmp = new t.constructor();
                for (var i = 0; i < as.length; ++i) {
                    tmp.add(as[i]);
                }
                return unifyAux(x, tt, tmp, trail);
            }
            case TypeChecker.types.TupleType: {
                var ts = t.inner();
                var as = a.inner();
                if (ts.length !== as.length)
                    return false;
                for (var i = 0; i < ts.length; ++i) {
                    if (!aux(unifyAux(x, ts[i], as[i], trail)))
                        return false;
                }
                return tmp;
            }
            case TypeChecker.types.ExistsType:
            case TypeChecker.types.ForallType: {
                var tb = t.bound();
                var ab = a.bound();
                if (((tb === null) !== (ab === null)) ||
                    (tb === null && ab === null && !aux(unifyAux(x, tb, ab, trail))))
                    return false;
                var xi = shift1(x, 0);
                var ti = t.inner();
                var ai = a.inner();
                if (!aux(unifyAux(xi, ti, ai, trail)))
                    return false;
                return tmp;
            }
            case TypeChecker.types.ReferenceType: {
                return unifyAux(x, t.location(), a.location(), trail);
            }
            case TypeChecker.types.StackedType: {
                if (!aux(unifyAux(x, t.left(), a.left(), trail)) ||
                    !aux(unifyAux(x, t.right(), a.right(), trail)))
                    return false;
                return tmp;
            }
            case TypeChecker.types.CapabilityType: {
                if (!aux(unifyAux(x, t.location(), a.location(), trail)) ||
                    !aux(unifyAux(x, t.value(), a.value(), trail)))
                    return false;
                return tmp;
            }
            case TypeChecker.types.RecordType: {
                var ts_2 = t.fields();
                var as_2 = a.fields();
                if (t.length() !== a.length())
                    return false;
                for (var i in ts_2) {
                    var ti_1 = ts_2[i];
                    var ai_1 = as_2[i];
                    if (ai_1 === undefined || !aux(unifyAux(x, ti_1, ai_1, trail)))
                        return false;
                }
                return tmp;
            }
            case TypeChecker.types.LocationVariable:
            case TypeChecker.types.TypeVariable:
                return t.index() === a.index();
            case TypeChecker.types.PrimitiveType:
                return t.name() === a.name();
            case TypeChecker.types.NoneType:
            case TypeChecker.types.TopType:
                return true;
            default:
                TypeChecker.error("@unifyAux: Not expecting " + t.type);
        }
    }
    ;
    function shift(t, c, d) {
        switch (t.type) {
            case TypeChecker.types.FunctionType:
                return new TypeChecker.FunctionType(shift(t.argument(), c, d), shift(t.body(), c, d));
            case TypeChecker.types.BangType:
                return new TypeChecker.BangType(shift(t.inner(), c, d));
            case TypeChecker.types.RelyType:
                return new TypeChecker.RelyType(shift(t.rely(), c, d), shift(t.guarantee(), c, d));
            case TypeChecker.types.GuaranteeType:
                return new TypeChecker.GuaranteeType(shift(t.guarantee(), c, d), shift(t.rely(), c, d));
            case TypeChecker.types.SumType: {
                var sum = new TypeChecker.SumType();
                var ts = t.tags();
                for (var k in ts) {
                    sum.add(ts[k], shift(t.inner(ts[k]), c, d));
                }
                return sum;
            }
            case TypeChecker.types.AlternativeType:
            case TypeChecker.types.IntersectionType:
            case TypeChecker.types.StarType:
            case TypeChecker.types.TupleType: {
                var star = new t.constructor();
                var inners = t.inner();
                for (var i = 0; i < inners.length; ++i) {
                    star.add(shift(inners[i], c, d));
                }
                return star;
            }
            case TypeChecker.types.ExistsType:
            case TypeChecker.types.ForallType: {
                return new t.constructor(t.id(), shift(t.inner(), c + 1, d), (t.bound() !== null ? shift(t.bound(), c, d) : null));
            }
            case TypeChecker.types.ReferenceType:
                return new TypeChecker.ReferenceType(shift(t.location(), c, d));
            case TypeChecker.types.StackedType:
                return new TypeChecker.StackedType(shift(t.left(), c, d), shift(t.right(), c, d));
            case TypeChecker.types.CapabilityType:
                return new TypeChecker.CapabilityType(shift(t.location(), c, d), shift(t.value(), c, d));
            case TypeChecker.types.RecordType: {
                var r = new TypeChecker.RecordType();
                var fs_1 = t.fields();
                for (var k in fs_1) {
                    r.add(k, shift(fs_1[k], c, d));
                }
                return r;
            }
            case TypeChecker.types.DefinitionType: {
                var fs = t.args();
                var tmp = new Array(fs.length);
                for (var i = 0; i < fs.length; ++i)
                    tmp[i] = shift(fs[i], c, d);
                return new TypeChecker.DefinitionType(t.definition(), tmp, t.getTypeDef());
            }
            case TypeChecker.types.LocationVariable:
            case TypeChecker.types.TypeVariable:
                if (t.index() < c)
                    return t;
                return t.copy(t.index() + d);
            case TypeChecker.types.PrimitiveType:
            case TypeChecker.types.NoneType:
            case TypeChecker.types.TopType:
                return t;
            default:
                TypeChecker.error("@shift: Not expecting " + t.type);
        }
    }
    TypeChecker.shift = shift;
    ;
    function shift1(t, c) {
        return shift(t, c, 1);
    }
    TypeChecker.shift1 = shift1;
    ;
    function rebase(a) {
        var s = indexSet(a);
        if (s.size > 0) {
            var v = [];
            s.forEach(function (val) { return v.push(val); });
            v.sort();
            for (var i = 0; i < v.length; ++i) {
                if (v[i] !== i) {
                    a = shift(a, i, i - v[i]);
                }
            }
        }
        return a;
    }
    ;
    function keyF(a, b) {
        a = rebase(a);
        b = rebase(b);
        return a.toString(true) + b.toString(true);
    }
    ;
    function equals(t1, t2) {
        return equalsAux(t1, t2, new Set());
    }
    TypeChecker.equals = equals;
    ;
    function equalsAux(t1, t2, trail) {
        if (t1 === t2)
            return true;
        var def1 = t1.type === TypeChecker.types.DefinitionType;
        var def2 = t2.type === TypeChecker.types.DefinitionType;
        if (def1 || def2) {
            var key = keyF(t1, t2);
            if (trail.has(key))
                return true;
            trail.add(key);
            t1 = def1 ? unfold(t1) : t1;
            t2 = def2 ? unfold(t2) : t2;
            return equalsAux(t1, t2, trail);
        }
        if (t1.type !== t2.type)
            return false;
        switch (t1.type) {
            case TypeChecker.types.ForallType:
            case TypeChecker.types.ExistsType: {
                if (t1.id().type !== t2.id().type)
                    return false;
                return equalsAux(t1.bound(), t2.bound(), trail) &&
                    equalsAux(t1.inner(), t2.inner(), trail);
            }
            case TypeChecker.types.TypeVariable:
            case TypeChecker.types.LocationVariable: {
                return t1.index() === t2.index();
            }
            case TypeChecker.types.FunctionType:
                return equalsAux(t1.argument(), t2.argument(), trail) &&
                    equalsAux(t1.body(), t2.body(), trail);
            case TypeChecker.types.BangType:
                return equalsAux(t1.inner(), t2.inner(), trail);
            case TypeChecker.types.RelyType: {
                return equalsAux(t1.rely(), t2.rely(), trail) &&
                    equalsAux(t1.guarantee(), t2.guarantee(), trail);
            }
            case TypeChecker.types.GuaranteeType: {
                return equalsAux(t1.guarantee(), t2.guarantee(), trail) &&
                    equalsAux(t1.rely(), t2.rely(), trail);
            }
            case TypeChecker.types.SumType: {
                var t1s_1 = t1.tags();
                var t2s_1 = t2.tags();
                if (t1.length() !== t2.length())
                    return false;
                for (var i_1 in t1s_1) {
                    var tt = t1.inner(t1s_1[i_1]);
                    var at = t2.inner(t1s_1[i_1]);
                    if (at === undefined || !equalsAux(tt, at, trail))
                        return false;
                }
                return true;
            }
            case TypeChecker.types.ReferenceType:
                return equalsAux(t1.location(), t2.location(), trail);
            case TypeChecker.types.StackedType:
                return equalsAux(t1.left(), t2.left(), trail) &&
                    equalsAux(t1.right(), t2.right(), trail);
            case TypeChecker.types.CapabilityType:
                return equalsAux(t1.location(), t2.location(), trail) &&
                    equalsAux(t1.value(), t2.value(), trail);
            case TypeChecker.types.RecordType: {
                var t1s_2 = t1.fields();
                var t2s_2 = t2.fields();
                if (t1.length() !== t2.length())
                    return false;
                for (var i_2 in t2s_2) {
                    var f1 = t1s_2[i_2];
                    var f2 = t2s_2[i_2];
                    if (f1 === undefined || !equalsAux(f1, f2, trail))
                        return false;
                }
                return true;
            }
            case TypeChecker.types.TupleType: {
                var t1s = t1.inner();
                var t2s = t2.inner();
                if (t1s.length !== t2s.length)
                    return false;
                for (var i = 0; i < t1s.length; ++i)
                    if (!equalsAux(t1s[i], t2s[i], trail))
                        return false;
                return true;
            }
            case TypeChecker.types.PrimitiveType:
                return t1.name() === t2.name();
            case TypeChecker.types.IntersectionType:
            case TypeChecker.types.AlternativeType:
            case TypeChecker.types.StarType: {
                var i1s = t1.inner();
                var i2s = t2.inner();
                if (i1s.length !== i2s.length)
                    return false;
                var tmp_i2s = i2s.slice(0);
                for (var i = 0; i < i1s.length; ++i) {
                    var curr = i1s[i];
                    var found = false;
                    for (var j = 0; j < tmp_i2s.length; ++j) {
                        var tmp = tmp_i2s[j];
                        if (equalsAux(curr, tmp, trail)) {
                            tmp_i2s.splice(j, 1);
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        return false;
                    }
                }
                return true;
            }
            default:
                TypeChecker.error("@equals: Not expecting " + t2.type);
        }
    }
    ;
    function substitutionAux(t, from, to) {
        var rec = function (type) {
            return substitutionAux(type, from, to);
        };
        if (t.type === from.type && t.index() === from.index())
            return to;
        switch (t.type) {
            case TypeChecker.types.FunctionType:
                return new TypeChecker.FunctionType(rec(t.argument()), rec(t.body()));
            case TypeChecker.types.BangType:
                return new TypeChecker.BangType(rec(t.inner()));
            case TypeChecker.types.RelyType:
                return new TypeChecker.RelyType(rec(t.rely()), rec(t.guarantee()));
            case TypeChecker.types.GuaranteeType:
                return new TypeChecker.GuaranteeType(rec(t.guarantee()), rec(t.rely()));
            case TypeChecker.types.SumType: {
                var sum = new TypeChecker.SumType();
                var ts = t.tags();
                for (var k in ts) {
                    sum.add(ts[k], rec(t.inner(ts[k])));
                }
                return sum;
            }
            case TypeChecker.types.AlternativeType:
            case TypeChecker.types.IntersectionType:
            case TypeChecker.types.StarType:
            case TypeChecker.types.TupleType: {
                var star = new t.constructor();
                var inners = t.inner();
                for (var i = 0; i < inners.length; ++i) {
                    star.add(rec(inners[i]));
                }
                return star;
            }
            case TypeChecker.types.ExistsType:
            case TypeChecker.types.ForallType: {
                var nvar = t.id();
                var ninner = t.inner();
                var nbound = t.bound();
                if (nbound !== null) {
                    nbound = substitutionAux(nbound, from, to);
                }
                var _to = shift1(to, 0);
                var _from = shift1(from, 0);
                return new t.constructor(nvar, substitutionAux(ninner, _from, _to), nbound);
            }
            case TypeChecker.types.ReferenceType:
                return new TypeChecker.ReferenceType(rec(t.location()));
            case TypeChecker.types.StackedType:
                return new TypeChecker.StackedType(rec(t.left()), rec(t.right()));
            case TypeChecker.types.CapabilityType:
                return new TypeChecker.CapabilityType(rec(t.location()), rec(t.value()));
            case TypeChecker.types.RecordType: {
                var r = new TypeChecker.RecordType();
                var fs_2 = t.fields();
                for (var k in fs_2) {
                    r.add(k, rec(fs_2[k]));
                }
                return r;
            }
            case TypeChecker.types.DefinitionType: {
                var fs = t.args();
                var tmp = new Array(fs.length);
                for (var i = 0; i < fs.length; ++i)
                    tmp[i] = rec(fs[i]);
                return new TypeChecker.DefinitionType(t.definition(), tmp, t.getTypeDef());
            }
            case TypeChecker.types.LocationVariable:
            case TypeChecker.types.TypeVariable:
            case TypeChecker.types.PrimitiveType:
            case TypeChecker.types.NoneType:
            case TypeChecker.types.TopType:
                return t;
            default:
                TypeChecker.error("@substitutionAux: Not expecting " + t.type);
        }
    }
    ;
    function substitution(type, from, to) {
        return substitutionAux(type, from, to);
    }
    TypeChecker.substitution = substitution;
    ;
    function subtype(t1, t2) {
        return subtypeAux(t1, t2, new Set());
    }
    TypeChecker.subtype = subtype;
    ;
    function subtypeAux(t1, t2, trail) {
        if (t1 === t2 || equals(t1, t2))
            return true;
        if (t1 instanceof TypeChecker.PrimitiveType && t2 instanceof TypeChecker.PrimitiveType) {
            return t1.name() === t2.name();
        }
        var def1 = t1 instanceof TypeChecker.DefinitionType;
        var def2 = t2 instanceof TypeChecker.DefinitionType;
        if (def1 || def2) {
            var key = keyF(t1, t2);
            if (trail.has(key))
                return true;
            trail.add(key);
            t1 = def1 ? unfold(t1) : t1;
            t2 = def2 ? unfold(t2) : t2;
            return subtypeAux(t1, t2, trail);
        }
        if (t2 instanceof TypeChecker.TopType)
            return true;
        if (t1 instanceof TypeChecker.TypeVariable) {
            var bound = t1.bound();
            if (bound !== null && subtypeAux(bound, t2, trail))
                return true;
        }
        if (t1 instanceof TypeChecker.BangType && subtypeAux(t1.inner(), t2, trail)) {
            return true;
        }
        if (t1 instanceof TypeChecker.BangType && t2 instanceof TypeChecker.BangType) {
            var i = t2.inner();
            if (i instanceof TypeChecker.RecordType && i.isEmpty())
                return true;
        }
        if (t1 instanceof TypeChecker.BangType && t2 instanceof TypeChecker.BangType && subtypeAux(t1.inner(), t2.inner(), trail)) {
            return true;
        }
        if (t1 instanceof TypeChecker.FunctionType && t2 instanceof TypeChecker.FunctionType &&
            subtypeAux(t2.argument(), t1.argument(), trail) && subtypeAux(t1.body(), t2.body(), trail)) {
            return true;
        }
        if (t1 instanceof TypeChecker.StackedType && t2 instanceof TypeChecker.StackedType &&
            subtypeAux(t1.left(), t2.left(), trail) && subtypeAux(t1.right(), t2.right(), trail)) {
            return true;
        }
        if (t1 instanceof TypeChecker.CapabilityType && t2 instanceof TypeChecker.CapabilityType &&
            equals(t1.location(), t2.location()) &&
            subtypeAux(t1.value(), t2.value(), trail)) {
            return true;
        }
        if (t1 instanceof TypeChecker.StarType && t2 instanceof TypeChecker.StarType) {
            var i1s = t1.inner();
            var i2s = t2.inner();
            if (i1s.length === i2s.length) {
                var tmp_i2s = i2s.slice(0);
                var fail = false;
                for (var _i = 0; _i < i1s.length; _i++) {
                    var curr = i1s[_i];
                    var found = false;
                    for (var _a = 0; _a < tmp_i2s.length; _a++) {
                        var tmp = tmp_i2s[_a];
                        for (var j = 0; j < tmp_i2s.length; ++j) {
                            var tmp_1 = tmp_i2s[j];
                            if (subtypeAux(curr, tmp_1, trail)) {
                                tmp_i2s.splice(j, 1);
                                found = true;
                                break;
                            }
                        }
                    }
                    if (!found) {
                        fail = true;
                        break;
                    }
                }
                if (!fail) {
                    return true;
                }
            }
        }
        if ((t1 instanceof TypeChecker.ExistsType && t2 instanceof TypeChecker.ExistsType) ||
            (t1 instanceof TypeChecker.ForallType && t2 instanceof TypeChecker.ForallType)) {
            if ((t1.id().type === t2.id().type) &&
                equals(t1.bound(), t2.bound()) &&
                subtypeAux(t1.inner(), t2.inner(), trail))
                return true;
        }
        if (t2 instanceof TypeChecker.ExistsType && !(t1 instanceof TypeChecker.ExistsType)) {
            var t1_s = shift1(t1, 0);
            var u = unify(t2.id(), t2.inner(), t1_s);
            if (u === false)
                return false;
            if (u === true)
                return true;
            var b = t2.bound();
            return b === null || subtypeAux(u, b, trail);
        }
        if (t1 instanceof TypeChecker.ForallType && !(t2 instanceof TypeChecker.ForallType)) {
            var t2_s = shift1(t2, 0);
            var u = unify(t1.id(), t1.inner(), t2_s);
            if (u === false)
                return false;
            if (u === true)
                return true;
            var b = t1.bound();
            return b === null || subtypeAux(u, b, trail);
        }
        if (t1 instanceof TypeChecker.RecordType && t2 instanceof TypeChecker.RecordType) {
            if (!t1.isEmpty() && t2.isEmpty())
                return false;
            var t1fields = t1.fields();
            var t2fields = t2.fields();
            for (var k in t2fields) {
                if (t1fields[k] === undefined ||
                    !subtypeAux(t1fields[k], t2fields[k], trail)) {
                    return false;
                }
            }
            return true;
        }
        if (t1 instanceof TypeChecker.SumType && t2 instanceof TypeChecker.SumType) {
            var t1_tags = t1.tags();
            for (var k in t1_tags) {
                if (t2.inner(t1_tags[k]) === undefined ||
                    !subtypeAux(t1.inner(t1_tags[k]), t2.inner(t1_tags[k]), trail))
                    return false;
            }
            return true;
        }
        if (t1 instanceof TypeChecker.TupleType && t2 instanceof TypeChecker.TupleType) {
            var t1s = t1.inner();
            var t2s = t2.inner();
            if (t1s.length !== t2s.length)
                return false;
            for (var i = 0; i < t1s.length; ++i)
                if (!subtypeAux(t1s[i], t2s[i], trail))
                    return false;
            return true;
        }
        if (!(t1 instanceof TypeChecker.AlternativeType) && t2 instanceof TypeChecker.AlternativeType) {
            var i2s = t2.inner();
            for (var j = 0; j < i2s.length; ++j) {
                if (subtypeAux(t1, i2s[j], trail)) {
                    return true;
                }
            }
        }
        if (t1 instanceof TypeChecker.AlternativeType && t2 instanceof TypeChecker.AlternativeType) {
            var i1s = t1.inner();
            var i2s = t2.inner();
            if (i1s.length > i2s.length)
                return false;
            var tmp_i2s = i2s.slice(0);
            for (var i = 0; i < i1s.length; ++i) {
                var curr = i1s[i];
                var found = false;
                for (var j = 0; j < tmp_i2s.length; ++j) {
                    var tmp = tmp_i2s[j];
                    if (subtypeAux(curr, tmp, trail)) {
                        tmp_i2s.splice(j, 1);
                        found = true;
                        break;
                    }
                }
                if (!found)
                    return false;
            }
            return true;
        }
        if (t1 instanceof TypeChecker.IntersectionType && !(t2 instanceof TypeChecker.IntersectionType)) {
            var i1s = t1.inner();
            for (var j = 0; j < i1s.length; ++j) {
                if (subtypeAux(i1s[j], t2, trail)) {
                    return true;
                }
            }
        }
        if (t1 instanceof TypeChecker.IntersectionType && t2 instanceof TypeChecker.IntersectionType) {
            var i1s = t2.inner();
            var i2s = t1.inner();
            if (i1s.length > i2s.length)
                return false;
            var tmp_i2s = i2s.slice(0);
            for (var i = 0; i < i1s.length; ++i) {
                var curr = i1s[i];
                var found = false;
                for (var j = 0; j < tmp_i2s.length; ++j) {
                    var tmp = tmp_i2s[j];
                    if (subtypeAux(curr, tmp, trail)) {
                        tmp_i2s.splice(j, 1);
                        found = true;
                        break;
                    }
                }
                if (!found)
                    return false;
            }
            return true;
        }
        return false;
    }
    ;
    function isFree(x, t) {
        return isFreeAux(x, t, new Set());
    }
    TypeChecker.isFree = isFree;
    ;
    function isFreeAux(x, t, trail) {
        if (t.type === TypeChecker.types.DefinitionType) {
            var key = t.toString(true);
            if (trail.has(key))
                return true;
            trail.add(key);
            return isFreeAux(x, unfold(t), trail);
        }
        switch (t.type) {
            case TypeChecker.types.NoneType:
            case TypeChecker.types.PrimitiveType:
                return true;
            case TypeChecker.types.BangType:
                return isFreeAux(x, t.inner(), trail);
            case TypeChecker.types.ReferenceType:
                return isFreeAux(x, t.location(), trail);
            case TypeChecker.types.RelyType: {
                return isFreeAux(x, t.rely(), trail) &&
                    isFreeAux(x, t.guarantee(), trail);
            }
            case TypeChecker.types.GuaranteeType: {
                return isFreeAux(x, t.guarantee(), trail) &&
                    isFreeAux(x, t.rely(), trail);
            }
            case TypeChecker.types.FunctionType:
                return isFreeAux(x, t.argument(), trail)
                    && isFreeAux(x, t.body(), trail);
            case TypeChecker.types.RecordType: {
                var fields = t.fields();
                for (var k in fields) {
                    if (!isFreeAux(x, fields[k], trail))
                        return false;
                }
                return true;
            }
            case TypeChecker.types.StackedType:
                return isFreeAux(x, t.left(), trail) &&
                    isFreeAux(x, t.right(), trail);
            case TypeChecker.types.CapabilityType:
                return isFreeAux(x, t.location(), trail) &&
                    isFreeAux(x, t.value(), trail);
            case TypeChecker.types.AlternativeType:
            case TypeChecker.types.IntersectionType:
            case TypeChecker.types.StarType:
            case TypeChecker.types.TupleType: {
                var ts = t.inner();
                for (var i = 0; i < ts.length; ++i)
                    if (!isFreeAux(x, ts[i], trail))
                        return false;
                return true;
            }
            case TypeChecker.types.SumType: {
                var ts = t.tags();
                for (var k in ts) {
                    if (!isFreeAux(x, t.inner(ts[k]), trail))
                        return false;
                }
                return true;
            }
            case TypeChecker.types.ForallType:
            case TypeChecker.types.ExistsType: {
                return (t.bound() === null || isFreeAux(x, t.bound(), trail)) &&
                    isFreeAux(shift(x, 0, 1), t.inner(), trail);
            }
            case TypeChecker.types.TypeVariable:
            case TypeChecker.types.LocationVariable:
                return x.type !== t.type || x.index() !== t.index();
            default:
                TypeChecker.error("@isFreeAux: Not expecting " + t.type);
        }
    }
    ;
    function unfold(t) {
        while (t.type === TypeChecker.types.DefinitionType) {
            t = unfoldDefinition(t);
        }
        return t;
    }
    TypeChecker.unfold = unfold;
    ;
    function unfoldDefinition(d) {
        if (d instanceof TypeChecker.DefinitionType) {
            var t = d.getDefinition();
            var args = d.args();
            var pars = d.getParams();
            for (var i = (args.length - 1); i >= 0; --i) {
                t = substitution(t, pars[i], shift(args[i], 0, pars.length));
            }
            t = shift(t, 0, -pars.length);
            return t;
        }
        return d;
    }
    TypeChecker.unfoldDefinition = unfoldDefinition;
    ;
    function indexSet(t) {
        var set = new Set();
        indexSetAux(t, 0, set);
        return set;
    }
    TypeChecker.indexSet = indexSet;
    ;
    function indexSetAux(t, c, set) {
        switch (t.type) {
            case TypeChecker.types.BangType: {
                indexSetAux(t.inner(), c, set);
                return;
            }
            case TypeChecker.types.ReferenceType: {
                indexSetAux(t.location(), c, set);
                return;
            }
            case TypeChecker.types.RelyType:
            case TypeChecker.types.GuaranteeType: {
                indexSetAux(t.rely(), c, set);
                indexSetAux(t.guarantee(), c, set);
                return;
            }
            case TypeChecker.types.FunctionType: {
                indexSetAux(t.argument(), c, set);
                indexSetAux(t.body(), c, set);
                return;
            }
            case TypeChecker.types.RecordType: {
                var fields = t.fields();
                for (var k in fields) {
                    indexSetAux(fields[k], c, set);
                }
                return;
            }
            case TypeChecker.types.StackedType: {
                indexSetAux(t.left(), c, set);
                indexSetAux(t.right(), c, set);
                return;
            }
            case TypeChecker.types.CapabilityType: {
                indexSetAux(t.location(), c, set);
                indexSetAux(t.value(), c, set);
                return;
            }
            case TypeChecker.types.AlternativeType:
            case TypeChecker.types.IntersectionType:
            case TypeChecker.types.StarType:
            case TypeChecker.types.TupleType: {
                var ts = t.inner();
                for (var i = 0; i < ts.length; ++i) {
                    indexSetAux(ts[i], c, set);
                }
                return;
            }
            case TypeChecker.types.SumType: {
                var ts = t.tags();
                for (var k in ts) {
                    indexSetAux(t.inner(ts[k]), c, set);
                }
                return;
            }
            case TypeChecker.types.ForallType:
            case TypeChecker.types.ExistsType: {
                if (t.bound() !== null) {
                    indexSetAux(t.bound(), c, set);
                }
                indexSetAux(t.inner(), c + 1, set);
                return;
            }
            case TypeChecker.types.TypeVariable:
            case TypeChecker.types.LocationVariable: {
                if (t.index() >= c) {
                    set.add(t.index() - c);
                }
                return;
            }
            case TypeChecker.types.DefinitionType: {
                var ts = t.args();
                for (var i = 0; i < ts.length; ++i) {
                    indexSetAux(ts[i], c, set);
                }
                return;
            }
            default:
                return;
        }
    }
    ;
})(TypeChecker || (TypeChecker = {}));
;
