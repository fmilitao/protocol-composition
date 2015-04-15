// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
var TypeChecker = (function (exports) {
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
    var NoneType = new fct.NoneType();
    var TopType = new fct.TopType();
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
    var unify = function (x, t, a) {
        if (x.type !== types.LocationVariable &&
            x.type !== types.TypeVariable) {
            error("@unify: can only unify a Type/LocationVariable, got: " + x.type);
        }
        return unifyAux(x, t, a, new Set());
    };
    var unifyAux = function (x, t, a, trail) {
        if (x.type === t.type && x.index() === t.index() && ((x.type === types.LocationVariable && a.type === types.LocationVariable) ||
            (x.type === types.TypeVariable && a.type !== types.LocationVariable)))
            return a;
        var deft = t.type === types.DefinitionType;
        var defa = a.type === types.DefinitionType;
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
            case types.FunctionType: {
                if (!aux(unifyAux(x, t.argument(), a.argument(), trail)) ||
                    !aux(unifyAux(x, t.body(), a.body(), trail)))
                    return false;
                return tmp;
            }
            case types.BangType:
                return unifyAux(x, t.inner(), a.inner(), trail);
            case types.RelyType:
            case types.GuaranteeType: {
                if (!aux(unifyAux(x, t.rely(), a.rely(), trail)) ||
                    !aux(unifyAux(x, t.guarantee(), a.guarantee(), trail)))
                    return false;
                return tmp;
            }
            case types.SumType: {
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
            case types.AlternativeType:
            case types.IntersectionType:
            case types.StarType: {
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
            case types.TupleType: {
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
            case types.ExistsType:
            case types.ForallType: {
                var tb = t.bound();
                var ab = a.bound();
                if (((tb === null) ^ (ab === null)) ||
                    (tb === null && ab === null && !aux(unifyAux(x, tb, ab, trail))))
                    return false;
                var xi = shift1(x, 0);
                var ti = t.inner();
                var ai = a.inner();
                if (!aux(unifyAux(xi, ti, ai, trail)))
                    return false;
                return tmp;
            }
            case types.ReferenceType: {
                return unifyAux(x, t.location(), a.location(), trail);
            }
            case types.StackedType: {
                if (!aux(unifyAux(x, t.left(), a.left(), trail)) ||
                    !aux(unifyAux(x, t.right(), a.right(), trail)))
                    return false;
                return tmp;
            }
            case types.CapabilityType: {
                if (!aux(unifyAux(x, t.location(), a.location(), trail)) ||
                    !aux(unifyAux(x, t.value(), a.value(), trail)))
                    return false;
                return tmp;
            }
            case types.RecordType: {
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
            case types.LocationVariable:
            case types.TypeVariable:
                return t.index() === a.index();
            case types.PrimitiveType:
                return t.name() === a.name();
            case types.NoneType:
            case types.TopType:
                return true;
            default:
                error("@unifyAux: Not expecting " + t.type);
        }
    };
    var shift = function (t, c, d) {
        switch (t.type) {
            case types.FunctionType:
                return new FunctionType(shift(t.argument(), c, d), shift(t.body(), c, d));
            case types.BangType:
                return new BangType(shift(t.inner(), c, d));
            case types.RelyType:
                return new RelyType(shift(t.rely(), c, d), shift(t.guarantee(), c, d));
            case types.GuaranteeType:
                return new GuaranteeType(shift(t.guarantee(), c, d), shift(t.rely(), c, d));
            case types.SumType: {
                var sum = new SumType();
                var ts = t.tags();
                for (var k in ts) {
                    sum.add(ts[k], shift(t.inner(ts[k]), c, d));
                }
                return sum;
            }
            case types.AlternativeType:
            case types.IntersectionType:
            case types.StarType:
            case types.TupleType: {
                var star = new t.constructor();
                var inners = t.inner();
                for (var i = 0; i < inners.length; ++i) {
                    star.add(shift(inners[i], c, d));
                }
                return star;
            }
            case types.ExistsType:
            case types.ForallType: {
                return new t.constructor(t.id(), shift(t.inner(), c + 1, d), (t.bound() !== null ? shift(t.bound(), c, d) : null));
            }
            case types.ReferenceType:
                return new ReferenceType(shift(t.location(), c, d));
            case types.StackedType:
                return new StackedType(shift(t.left(), c, d), shift(t.right(), c, d));
            case types.CapabilityType:
                return new CapabilityType(shift(t.location(), c, d), shift(t.value(), c, d));
            case types.RecordType: {
                var r = new RecordType();
                var fs_1 = t.fields();
                for (var k in fs_1) {
                    r.add(k, shift(fs_1[k], c, d));
                }
                return r;
            }
            case types.DefinitionType: {
                var fs = t.args();
                var tmp = new Array(fs.length);
                for (var i = 0; i < fs.length; ++i)
                    tmp[i] = shift(fs[i], c, d);
                return new DefinitionType(t.definition(), tmp, t.getTypeDef());
            }
            case types.LocationVariable:
            case types.TypeVariable:
                if (t.index() < c)
                    return t;
                return t.copy(t.index() + d);
            case types.PrimitiveType:
            case types.NoneType:
            case types.TopType:
                return t;
            default:
                error("@shift: Not expecting " + t.type);
        }
    };
    var shift1 = function (t, c) {
        return shift(t, c, 1);
    };
    var keyF = function (a, b) {
        var rebase = function (a) {
            var s = indexSet(a);
            if (s.size > 0) {
                var v = [];
                s.forEach(function (val) { v.push(val); });
                v.sort();
                for (var i = 0; i < v.length; ++i) {
                    if (v[i] !== i) {
                        a = shift(a, i, i - v[i]);
                    }
                }
            }
            return a;
        };
        a = rebase(a);
        b = rebase(b);
        return a.toString(true) + b.toString(true);
    };
    var equals = function (t1, t2) {
        return equalsAux(t1, t2, new Set());
    };
    var equalsAux = function (t1, t2, trail) {
        if (t1 === t2)
            return true;
        var def1 = t1.type === types.DefinitionType;
        var def2 = t2.type === types.DefinitionType;
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
            case types.ForallType:
            case types.ExistsType: {
                if (t1.id().type !== t2.id().type)
                    return false;
                return equalsAux(t1.bound(), t2.bound(), trail) &&
                    equalsAux(t1.inner(), t2.inner(), trail);
            }
            case types.TypeVariable:
            case types.LocationVariable: {
                return t1.index() === t2.index();
            }
            case types.FunctionType:
                return equalsAux(t1.argument(), t2.argument(), trail) &&
                    equalsAux(t1.body(), t2.body(), trail);
            case types.BangType:
                return equalsAux(t1.inner(), t2.inner(), trail);
            case types.RelyType: {
                return equalsAux(t1.rely(), t2.rely(), trail) &&
                    equalsAux(t1.guarantee(), t2.guarantee(), trail);
            }
            case types.GuaranteeType: {
                return equalsAux(t1.guarantee(), t2.guarantee(), trail) &&
                    equalsAux(t1.rely(), t2.rely(), trail);
            }
            case types.SumType: {
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
            case types.ReferenceType:
                return equalsAux(t1.location(), t2.location(), trail);
            case types.StackedType:
                return equalsAux(t1.left(), t2.left(), trail) &&
                    equalsAux(t1.right(), t2.right(), trail);
            case types.CapabilityType:
                return equalsAux(t1.location(), t2.location(), trail) &&
                    equalsAux(t1.value(), t2.value(), trail);
            case types.RecordType: {
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
            case types.TupleType: {
                var t1s = t1.inner();
                var t2s = t2.inner();
                if (t1s.length !== t2s.length)
                    return false;
                for (var i = 0; i < t1s.length; ++i)
                    if (!equalsAux(t1s[i], t2s[i], trail))
                        return false;
                return true;
            }
            case types.PrimitiveType:
                return t1.name() === t2.name();
            case types.IntersectionType:
            case types.AlternativeType:
            case types.StarType: {
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
                error("@equals: Not expecting " + t2.type);
        }
    };
    var substitutionAux = function (t, from, to) {
        var rec = function (type) {
            return substitutionAux(type, from, to);
        };
        if (t.type === from.type && t.index() === from.index())
            return to;
        switch (t.type) {
            case types.FunctionType:
                return new FunctionType(rec(t.argument()), rec(t.body()));
            case types.BangType:
                return new BangType(rec(t.inner()));
            case types.RelyType:
                return new RelyType(rec(t.rely()), rec(t.guarantee()));
            case types.GuaranteeType:
                return new GuaranteeType(rec(t.guarantee()), rec(t.rely()));
            case types.SumType: {
                var sum = new SumType();
                var ts = t.tags();
                for (var k in ts) {
                    sum.add(ts[k], rec(t.inner(ts[k])));
                }
                return sum;
            }
            case types.AlternativeType:
            case types.IntersectionType:
            case types.StarType:
            case types.TupleType: {
                var star = new t.constructor();
                var inners = t.inner();
                for (var i = 0; i < inners.length; ++i) {
                    star.add(rec(inners[i]));
                }
                return star;
            }
            case types.ExistsType:
            case types.ForallType: {
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
            case types.ReferenceType:
                return new ReferenceType(rec(t.location()));
            case types.StackedType:
                return new StackedType(rec(t.left()), rec(t.right()));
            case types.CapabilityType:
                return new CapabilityType(rec(t.location()), rec(t.value()));
            case types.RecordType: {
                var r = new RecordType();
                var fs_2 = t.fields();
                for (var k in fs_2) {
                    r.add(k, rec(fs_2[k]));
                }
                return r;
            }
            case types.DefinitionType: {
                var fs = t.args();
                var tmp = new Array(fs.length);
                for (var i = 0; i < fs.length; ++i)
                    tmp[i] = rec(fs[i]);
                return new DefinitionType(t.definition(), tmp, t.getTypeDef());
            }
            case types.LocationVariable:
            case types.TypeVariable:
            case types.PrimitiveType:
            case types.NoneType:
            case types.TopType:
                return t;
            default:
                error("@substitutionAux: Not expecting " + t.type);
        }
    };
    var substitution = function (type, from, to) {
        if (from.type !== types.LocationVariable &&
            from.type !== types.TypeVariable) {
            error("@substitution: can only substitute a Type/LocationVariable, got: " + from.type);
        }
        return substitutionAux(type, from, to);
    };
    var subtype = function (t1, t2) {
        return subtypeAux(t1, t2, new Set());
    };
    var subtypeAux = function (t1, t2, trail) {
        if (t1 === t2 || equals(t1, t2))
            return true;
        var def1 = t1.type === types.DefinitionType;
        var def2 = t2.type === types.DefinitionType;
        if (def1 || def2) {
            var key = keyF(t1, t2);
            if (trail.has(key))
                return true;
            trail.add(key);
            t1 = def1 ? unfold(t1) : t1;
            t2 = def2 ? unfold(t2) : t2;
            return subtypeAux(t1, t2, trail);
        }
        if (t2.type === types.TopType && t1.type !== types.LocationVariable)
            return true;
        if (t1.type === types.TypeVariable) {
            var bound = t1.bound();
            if (bound !== null && equals(bound, t2))
                return true;
        }
        if (t1.type === types.BangType && t2.type !== types.BangType)
            return subtypeAux(t1.inner(), t2, trail);
        if (t2.type === types.BangType &&
            (t1.type === types.ReferenceType
                || t1.type === types.PrimitiveType
                || (t1.type === types.RecordType && t1.isEmpty())))
            return subtypeAux(t1, t2.inner(), trail);
        if (t1.type === types.ReferenceType && t2.type === types.BangType)
            return subtypeAux(t1, t2.inner(), trail);
        if (t1.type === types.RecordType && t2.type === types.BangType &&
            equals(t1, t2.inner())) {
            var t1fields = t1.fields();
            var allPure = true;
            for (var i_3 in t1fields) {
                if (t1fields[i_3].type !== types.BangType) {
                    allPure = false;
                    break;
                }
            }
            if (allPure)
                return true;
        }
        if (t1.type !== types.AlternativeType && t2.type === types.AlternativeType) {
            var i2s = t2.inner();
            for (var j = 0; j < i2s.length; ++j) {
                if (subtypeAux(t1, i2s[j], trail)) {
                    return true;
                }
            }
            return false;
        }
        if (t1.type === types.IntersectionType && t2.type !== types.IntersectionType) {
            var i1s = t1.inner();
            for (var j = 0; j < i1s.length; ++j) {
                if (subtypeAux(i1s[j], t2, trail)) {
                    return true;
                }
            }
            return false;
        }
        if (t2.type === types.ExistsType && t1.type !== types.ExistsType) {
            var t1_s = shift1(t1, 0);
            var u = unify(t2.id(), t2.inner(), t1_s);
            if (u === false)
                return false;
            if (u === true)
                return true;
            var b = t2.bound();
            return b === null || subtypeAux(u, b, trail);
        }
        if (t1.type === types.ForallType && t2.type !== types.ForallType) {
            var t2_s = shift1(t2, 0);
            var u = unify(t1.id(), t1.inner(), t2_s);
            if (u === false)
                return false;
            if (u === true)
                return true;
            var b = t1.bound();
            return b === null || subtypeAux(u, b, trail);
        }
        if (t1.type !== t2.type) {
            return false;
        }
        switch (t1.type) {
            case types.NoneType:
                return true;
            case types.PrimitiveType:
                return t1.name() === t2.name();
            case types.BangType:
                if (t2.inner().type === types.RecordType && t2.inner().isEmpty())
                    return true;
                return subtypeAux(t1.inner(), t2.inner(), trail);
            case types.ReferenceType:
                return subtypeAux(t1.location(), t2.location(), trail);
            case types.RelyType:
            case types.GuaranteeType:
                return false;
            case types.FunctionType:
                return subtypeAux(t2.argument(), t1.argument(), trail)
                    && subtypeAux(t1.body(), t2.body(), trail);
            case types.RecordType: {
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
            case types.TupleType: {
                var t1s = t1.inner();
                var t2s = t2.inner();
                if (t1s.length !== t2s.length)
                    return false;
                for (var i = 0; i < t1s.length; ++i)
                    if (!subtypeAux(t1s[i], t2s[i], trail))
                        return false;
                return true;
            }
            case types.StackedType:
                return subtypeAux(t1.left(), t2.left(), trail) &&
                    subtypeAux(t1.right(), t2.right(), trail);
            case types.AlternativeType: {
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
            case types.IntersectionType: {
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
            case types.StarType: {
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
            case types.SumType: {
                var t1_tags = t1.tags();
                for (var k in t1_tags) {
                    if (t2.inner(t1_tags[k]) === undefined ||
                        !subtypeAux(t1.inner(t1_tags[k]), t2.inner(t1_tags[k]), trail))
                        return false;
                }
                return true;
            }
            case types.CapabilityType:
                return subtypeAux(t1.location(), t2.location(), trail) &&
                    subtypeAux(t1.value(), t2.value(), trail);
            case types.ForallType:
            case types.ExistsType: {
                if (t1.id().type !== t2.id().type)
                    return false;
                if (!equals(t1.bound(), t2.bound()))
                    return false;
                return subtypeAux(t1.inner(), t2.inner(), trail);
            }
            case types.TypeVariable:
            case types.LocationVariable:
                return t1.index() === t2.index();
            default:
                error("@subtypeAux: Not expecting " + t1.type);
        }
    };
    var isFree = function (x, t) {
        if (x.type !== types.LocationVariable &&
            x.type !== types.TypeVariable) {
            error("@isFree: can only check a Type/LocationVariable, got: " + x.type);
        }
        return isFreeAux(x, t, new Set());
    };
    var isFreeAux = function (x, t, trail) {
        if (t.type === types.DefinitionType) {
            var key = t.toString(true);
            if (trail.has(key))
                return true;
            trail.add(key);
            return isFreeAux(x, unfold(t), trail);
        }
        switch (t.type) {
            case types.NoneType:
            case types.PrimitiveType:
                return true;
            case types.BangType:
                return isFreeAux(x, t.inner(), trail);
            case types.ReferenceType:
                return isFreeAux(x, t.location(), trail);
            case types.RelyType: {
                return isFreeAux(x, t.rely(), trail) &&
                    isFreeAux(x, t.guarantee(), trail);
            }
            case types.GuaranteeType: {
                return isFreeAux(x, t.guarantee(), trail) &&
                    isFreeAux(x, t.rely(), trail);
            }
            case types.FunctionType:
                return isFreeAux(x, t.argument(), trail)
                    && isFreeAux(x, t.body(), trail);
            case types.RecordType: {
                var fields = t.fields();
                for (var k in fields) {
                    if (!isFreeAux(x, fields[k], trail))
                        return false;
                }
                return true;
            }
            case types.StackedType:
                return isFreeAux(x, t.left(), trail) &&
                    isFreeAux(x, t.right(), trail);
            case types.CapabilityType:
                return isFreeAux(x, t.location(), trail) &&
                    isFreeAux(x, t.value(), trail);
            case types.AlternativeType:
            case types.IntersectionType:
            case types.StarType:
            case types.TupleType: {
                var ts = t.inner();
                for (var i = 0; i < ts.length; ++i)
                    if (!isFreeAux(x, ts[i], trail))
                        return false;
                return true;
            }
            case types.SumType: {
                var ts = t.tags();
                for (var k in ts) {
                    if (!isFreeAux(x, t.inner(ts[k]), trail))
                        return false;
                }
                return true;
            }
            case types.ForallType:
            case types.ExistsType: {
                return (t.bound() === null || isFreeAux(x, t.bound(), trail)) &&
                    isFreeAux(shift(x, 0, 1), t.inner(), trail);
            }
            case types.TypeVariable:
            case types.LocationVariable:
                return x.type !== t.type || x.index() !== t.index();
            default:
                error("@isFreeAux: Not expecting " + t.type);
        }
    };
    var unfold = function (t) {
        while (t.type === types.DefinitionType) {
            t = unfoldDefinition(t);
        }
        return t;
    };
    var unfoldDefinition = function (d) {
        if (d.type !== types.DefinitionType)
            return d;
        var t = d.getDefinition();
        var args = d.args();
        var pars = d.getParams();
        for (var i = (args.length - 1); i >= 0; --i) {
            t = substitution(t, pars[i], shift(args[i], 0, pars.length));
        }
        t = shift(t, 0, -pars.length);
        return t;
    };
    var indexSet = function (t) {
        var set = new Set();
        indexSetAux(t, 0, set);
        return set;
    };
    var indexSetAux = function (t, c, set) {
        switch (t.type) {
            case types.BangType: {
                indexSetAux(t.inner(), c, set);
                return;
            }
            case types.ReferenceType: {
                indexSetAux(t.location(), c, set);
                return;
            }
            case types.RelyType:
            case types.GuaranteeType: {
                indexSetAux(t.rely(), c, set);
                indexSetAux(t.guarantee(), c, set);
                return;
            }
            case types.FunctionType: {
                indexSetAux(t.argument(), c, set);
                indexSetAux(t.body(), c, set);
                return;
            }
            case types.RecordType: {
                var fields = t.fields();
                for (var k in fields) {
                    indexSetAux(fields[k], c, set);
                }
                return;
            }
            case types.StackedType: {
                indexSetAux(t.left(), c, set);
                indexSetAux(t.right(), c, set);
                return;
            }
            case types.CapabilityType: {
                indexSetAux(t.location(), c, set);
                indexSetAux(t.value(), c, set);
                return;
            }
            case types.AlternativeType:
            case types.IntersectionType:
            case types.StarType:
            case types.TupleType: {
                var ts = t.inner();
                for (var i = 0; i < ts.length; ++i) {
                    indexSetAux(ts[i], c, set);
                }
                return;
            }
            case types.SumType: {
                var ts = t.tags();
                for (var k in ts) {
                    indexSetAux(t.inner(ts[k]), c, set);
                }
                return;
            }
            case types.ForallType:
            case types.ExistsType: {
                if (t.bound() !== null) {
                    indexSetAux(t.bound(), c, set);
                }
                indexSetAux(t.inner(), c + 1, set);
                return;
            }
            case types.TypeVariable:
            case types.LocationVariable: {
                if (t.index() >= c) {
                    set.add(t.index() - c);
                }
                return;
            }
            case types.DefinitionType: {
                var ts = t.args();
                for (var i = 0; i < ts.length; ++i) {
                    indexSetAux(ts[i], c, set);
                }
                return;
            }
            default:
                return;
        }
    };
    var isProtocol = function (t, trail) {
        switch (t.type) {
            case types.NoneType:
                return true;
            case types.RelyType:
                return true;
            case types.ExistsType:
                return isProtocol(t.inner(), trail);
            case types.AlternativeType:
            case types.IntersectionType:
            case types.StarType: {
                var ts = t.inner();
                for (var i = 0; i < ts.length; ++i) {
                    if (!isProtocol(ts[i], trail))
                        return false;
                }
                return true;
            }
            case types.DefinitionType: {
                if (trail === undefined) {
                    trail = new Set();
                }
                var key = t.toString(true);
                if (trail.has(key))
                    return true;
                trail.add(key);
                return isProtocol(unfold(t), trail);
            }
            default:
                return false;
        }
    };
    exports.shift = shift;
    exports.unify = unify;
    exports.unfold = unfold;
    exports.unfoldDefinition = unfoldDefinition;
    exports.substitution = substitution;
    exports.subtype = subtype;
    exports.equals = equals;
    exports.isFree = isFree;
    exports.isProtocol = isProtocol;
    exports.indexSet = indexSet;
    return exports;
})(TypeChecker);
