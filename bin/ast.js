// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/
var __extends = this.__extends || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    __.prototype = b.prototype;
    d.prototype = new __();
};
function ErrorWrapper(msg, kind, ast, debug, stack) {
    this.message = msg;
    this.kind = kind;
    this.ast = ast;
    this.debug = debug;
    this.stack = stack || (new Error()).stack.toString();
    this.toString = function () { kind + ': ' + msg; };
}
;
function assertF(kind, f, msg, ast) {
    var result = undefined;
    var error = true;
    var debug = null;
    try {
        if (f instanceof Function) {
            result = f();
            error = result === undefined;
        }
        else {
            result = f;
            error = result === undefined || result === false;
        }
    }
    catch (e) {
        if (e instanceof ErrorWrapper)
            throw e;
        if (e instanceof RangeError)
            msg = e.message;
        debug = (e || e.message);
    }
    if (error)
        throw new ErrorWrapper(msg, kind, ast, debug);
    return result;
}
;
var AST;
(function (AST) {
    function merge(kind, l, r) {
        var tmp = [];
        if (l.kind === kind) {
            tmp = tmp.concat(l.types);
        }
        else {
            tmp.push(l);
        }
        if (r.kind === kind) {
            tmp = tmp.concat(r.types);
        }
        else {
            tmp.push(r);
        }
        return tmp;
    }
    ;
    function unsafe_addKind(obj) {
        obj.prototype['kind'] = obj.name;
    }
    ;
    var BaseAST = (function () {
        function BaseAST(info) {
            if (info) {
                this.line = info.first_line - 1;
                this.col = info.first_column;
                this.last_line = info.last_line - 1;
                this.last_col = info.last_column;
            }
        }
        BaseAST.prototype.match = function (cases) {
            if (!cases.hasOwnProperty(this.kind))
                throw new Error('Missing: ' + this.kind + ' on ' + cases.constructor.name);
            return cases[this.kind](this);
        };
        return BaseAST;
    })();
    ;
    var Exp;
    (function (Exp) {
        ;
        ;
        var TypeDef = (function (_super) {
            __extends(TypeDef, _super);
            function TypeDef(id, type, pars, info) {
                _super.call(this, info);
                this.id = id;
                this.type = type;
                this.pars = pars;
            }
            return TypeDef;
        })(BaseAST);
        Exp.TypeDef = TypeDef;
        ;
        var Program = (function (_super) {
            __extends(Program, _super);
            function Program(typedefs, exp, info) {
                _super.call(this, info);
                this.typedefs = typedefs;
                this.exp = exp;
            }
            return Program;
        })(BaseAST);
        Exp.Program = Program;
        ;
        var Share = (function (_super) {
            __extends(Share, _super);
            function Share(value, type, a, b, info) {
                _super.call(this, info);
                this.value = value;
                this.type = type;
                this.a = a;
                this.b = b;
            }
            return Share;
        })(BaseAST);
        Exp.Share = Share;
        ;
        var Subtype = (function (_super) {
            __extends(Subtype, _super);
            function Subtype(value, a, b, info) {
                _super.call(this, info);
                this.value = value;
                this.a = a;
                this.b = b;
            }
            return Subtype;
        })(BaseAST);
        Exp.Subtype = Subtype;
        ;
        var Equals = (function (_super) {
            __extends(Equals, _super);
            function Equals(value, a, b, info) {
                _super.call(this, info);
                this.value = value;
                this.a = a;
                this.b = b;
            }
            return Equals;
        })(BaseAST);
        Exp.Equals = Equals;
        ;
        var Forall = (function (_super) {
            __extends(Forall, _super);
            function Forall(id, exp, bound, info) {
                _super.call(this, info);
                this.id = id;
                this.exp = exp;
                this.bound = bound;
            }
            return Forall;
        })(BaseAST);
        Exp.Forall = Forall;
        ;
        unsafe_addKind(TypeDef);
        unsafe_addKind(Program);
        unsafe_addKind(Share);
        unsafe_addKind(Subtype);
        unsafe_addKind(Equals);
        unsafe_addKind(Forall);
    })(Exp = AST.Exp || (AST.Exp = {}));
    ;
    var Type;
    (function (Type) {
        ;
        ;
        var Substitution = (function (_super) {
            __extends(Substitution, _super);
            function Substitution(type, to, from, info) {
                _super.call(this, info);
                this.type = type;
                this.to = to;
                this.from = from;
            }
            return Substitution;
        })(BaseAST);
        Type.Substitution = Substitution;
        ;
        var Exists = (function (_super) {
            __extends(Exists, _super);
            function Exists(id, exp, bound, info) {
                _super.call(this, info);
                this.id = id;
                this.exp = exp;
                this.bound = bound;
            }
            return Exists;
        })(BaseAST);
        Type.Exists = Exists;
        ;
        var Forall = (function (_super) {
            __extends(Forall, _super);
            function Forall(id, exp, bound, info) {
                _super.call(this, info);
                this.id = id;
                this.exp = exp;
                this.bound = bound;
            }
            return Forall;
        })(BaseAST);
        Type.Forall = Forall;
        ;
        var Stacked = (function (_super) {
            __extends(Stacked, _super);
            function Stacked(left, right, info) {
                _super.call(this, info);
                this.left = left;
                this.right = right;
            }
            return Stacked;
        })(BaseAST);
        Type.Stacked = Stacked;
        ;
        var Rely = (function (_super) {
            __extends(Rely, _super);
            function Rely(left, right, info) {
                _super.call(this, info);
                this.left = left;
                this.right = right;
            }
            return Rely;
        })(BaseAST);
        Type.Rely = Rely;
        ;
        var Guarantee = (function (_super) {
            __extends(Guarantee, _super);
            function Guarantee(left, right, info) {
                _super.call(this, info);
                this.left = left;
                this.right = right;
            }
            return Guarantee;
        })(BaseAST);
        Type.Guarantee = Guarantee;
        ;
        var Sum = (function (_super) {
            __extends(Sum, _super);
            function Sum(sums, info) {
                _super.call(this, info);
                this.sums = sums;
            }
            return Sum;
        })(BaseAST);
        Type.Sum = Sum;
        ;
        var Star = (function (_super) {
            __extends(Star, _super);
            function Star(left, right, info) {
                _super.call(this, info);
                this.types = merge(this.kind, left, right);
            }
            return Star;
        })(BaseAST);
        Type.Star = Star;
        ;
        var Intersection = (function (_super) {
            __extends(Intersection, _super);
            function Intersection(left, right, info) {
                _super.call(this, info);
                this.types = merge(this.kind, left, right);
            }
            return Intersection;
        })(BaseAST);
        Type.Intersection = Intersection;
        ;
        var Alternative = (function (_super) {
            __extends(Alternative, _super);
            function Alternative(left, right, info) {
                _super.call(this, info);
                this.types = merge(this.kind, left, right);
            }
            return Alternative;
        })(BaseAST);
        Type.Alternative = Alternative;
        ;
        var Function = (function (_super) {
            __extends(Function, _super);
            function Function(arg, exp, info) {
                _super.call(this, info);
                this.arg = arg;
                this.exp = exp;
            }
            return Function;
        })(BaseAST);
        Type.Function = Function;
        ;
        var Capability = (function (_super) {
            __extends(Capability, _super);
            function Capability(id, type, info) {
                _super.call(this, info);
                this.id = id;
                this.type = type;
            }
            return Capability;
        })(BaseAST);
        Type.Capability = Capability;
        ;
        var Name = (function (_super) {
            __extends(Name, _super);
            function Name(text, info) {
                _super.call(this, info);
                this.text = text;
            }
            return Name;
        })(BaseAST);
        Type.Name = Name;
        ;
        var Primitive = (function (_super) {
            __extends(Primitive, _super);
            function Primitive(text, info) {
                _super.call(this, info);
                this.text = text;
            }
            return Primitive;
        })(BaseAST);
        Type.Primitive = Primitive;
        ;
        var Reference = (function (_super) {
            __extends(Reference, _super);
            function Reference(text, info) {
                _super.call(this, info);
                this.text = text;
            }
            return Reference;
        })(BaseAST);
        Type.Reference = Reference;
        ;
        var Bang = (function (_super) {
            __extends(Bang, _super);
            function Bang(type, info) {
                _super.call(this, info);
                this.type = type;
            }
            return Bang;
        })(BaseAST);
        Type.Bang = Bang;
        ;
        var Record = (function (_super) {
            __extends(Record, _super);
            function Record(exp, info) {
                _super.call(this, info);
                this.exp = exp;
            }
            return Record;
        })(BaseAST);
        Type.Record = Record;
        ;
        var Field = (function (_super) {
            __extends(Field, _super);
            function Field(id, exp, info) {
                _super.call(this, info);
                this.id = id;
                this.exp = exp;
            }
            return Field;
        })(BaseAST);
        Type.Field = Field;
        ;
        var Tuple = (function (_super) {
            __extends(Tuple, _super);
            function Tuple(exp, info) {
                _super.call(this, info);
                this.exp = exp;
            }
            return Tuple;
        })(BaseAST);
        Type.Tuple = Tuple;
        ;
        var Tagged = (function (_super) {
            __extends(Tagged, _super);
            function Tagged(tag, exp, info) {
                _super.call(this, info);
                this.tag = tag;
                this.exp = exp;
            }
            return Tagged;
        })(BaseAST);
        Type.Tagged = Tagged;
        ;
        var None = (function (_super) {
            __extends(None, _super);
            function None(info) {
                _super.call(this, info);
            }
            return None;
        })(BaseAST);
        Type.None = None;
        ;
        var Top = (function (_super) {
            __extends(Top, _super);
            function Top(info) {
                _super.call(this, info);
            }
            return Top;
        })(BaseAST);
        Type.Top = Top;
        ;
        var Definition = (function (_super) {
            __extends(Definition, _super);
            function Definition(name, args, info) {
                _super.call(this, info);
                this.name = name;
                this.args = args;
            }
            return Definition;
        })(BaseAST);
        Type.Definition = Definition;
        ;
        unsafe_addKind(Substitution);
        unsafe_addKind(Exists);
        unsafe_addKind(Forall);
        unsafe_addKind(Stacked);
        unsafe_addKind(Rely);
        unsafe_addKind(Guarantee);
        unsafe_addKind(Sum);
        unsafe_addKind(Star);
        unsafe_addKind(Alternative);
        unsafe_addKind(Intersection);
        unsafe_addKind(Function);
        unsafe_addKind(Capability);
        unsafe_addKind(Name);
        unsafe_addKind(Primitive);
        unsafe_addKind(Reference);
        unsafe_addKind(Bang);
        unsafe_addKind(Record);
        unsafe_addKind(Field);
        unsafe_addKind(Tuple);
        unsafe_addKind(Tagged);
        unsafe_addKind(None);
        unsafe_addKind(Top);
        unsafe_addKind(Definition);
    })(Type = AST.Type || (AST.Type = {}));
    ;
})(AST || (AST = {}));
;
