// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/**
 * INCLUDE 'parser.js' (contains required global variables):
 *  assertf : for error handling/flagging.
 */

module TypeChecker {


    // these are program assertions and should never be seen by users
    // unless there is a major malfunction in the code (bug...)
    export function error(msg: string|boolean) {
        // if a boolean and true
        if (typeof (msg) === 'boolean' && msg)
            return;
        // else it should be a string with the type error
        assertF('Bug Alert', false, msg, undefined); // undefined blamed 'ast'
    };

    //
    // TYPES
    //

    export const types: any = {}; // types enumeration, useful for case analysis
    export const fct: any = {}; // types factory

    function unsafe_addNewType(obj) {
        const name = obj.name; // should be the type's name

        // duplication check
        error((!types.hasOwnProperty(name) && !fct.hasOwnProperty(name))
            || ('@unsafe_addNewType: already exists: ' + name));

        types[name] = name;
        fct[name] = obj;

        obj.prototype['type'] = name;
    };

    export interface Type {
        match<T>(m: MatchType<T>): T;
        toString(n: boolean): string; //FIXME wtf is 'n' ??
        type: string;
    };

    export interface MatchType<T> {
        FunctionType(x: FunctionType): T;
        BangType(x: BangType): T;
        SumType(x: SumType): T;
        StarType(x: StarType): T;
        AlternativeType(x: AlternativeType): T;
        IntersectionType(x: IntersectionType): T;
        TupleType(x: TupleType): T;
        ForallType(x: ForallType): T;
        ExistsType(x: ExistsType): T;
        RecordType(x: RecordType): T;
        NoneType(x: NoneType): T;
        TopType(x: TopType): T;
        ReferenceType(x: ReferenceType): T;
        StackedType(x: StackedType): T;
        CapabilityType(x: CapabilityType): T;
        LocationVariable(x: LocationVariable): T;
        TypeVariable(x: TypeVariable): T;
        PrimitiveType(x: PrimitiveType): T;
        RelyType(x: RelyType): T;
        GuaranteeType(x: GuaranteeType): T;
        DefinitionType(x: DefinitionType): T;
    };

    class BaseType implements Type {

        public type: string; // attached (statically) by 'unsafe_addNewType'
        public toString: (boolean) => string; // attached by 'setupToString'

        match<T>(cases: any): T {
            // for debugging:
            if (!cases.hasOwnProperty(this.type))
                throw new Error('Missing: ' + this.type + ' on ' + cases.constructor.name);

            // not very safe, but convenient way to do pattern matching within typescript
            return cases[this.type](<any>this);
        }
    };

    // all types are immutable.

    export class FunctionType extends BaseType {
        public argument: () => Type;
        public body: () => Type;

        constructor(
            argument: Type,
            body: Type
            ) {
            super();

            this.argument = () => argument;
            this.body = () => body;
        }
    };

    export class BangType extends BaseType {
        public inner: () => Type;

        constructor(inner: Type) {
            super();
            this.inner = () => inner;
        }
    };

    export class SumType extends BaseType {
        public add: (tag: string, inner: Type) => boolean;
        public tags: () => string[];
        public inner: (tag: string) => Type;
        public length: () => number;

        constructor() {
            super();

            let tags = {};

            this.add = function(tag, inner) {
                if (tags.hasOwnProperty(tag))
                    return false;
                tags[tag] = inner;
                return true;
            };
            this.tags = function() {
                return Object.keys(tags);
            };
            this.inner = function(tag) {
                return tags[tag];
            };
            this.length = function() {
                return Object.keys(tags).length;
            };
        }
    };

    class _Aux_ extends BaseType {
        public add: (inner: Type) => boolean;
        public inner: () => Type[];
        constructor() {
            super();
            let v: Type[] = [];
            this.add = function(inner) {
                v.push(inner);
                return true;
            };
            this.inner = function() { return v; };
        }

    }

    export class StarType extends _Aux_ {
        constructor() {
            super();
        }
    };

    export class AlternativeType extends _Aux_ {
        constructor() {
            super();
        }
    };

    export class IntersectionType extends _Aux_ {
        constructor() {
            super();
        }
    };

    export class TupleType extends _Aux_ {
        constructor() {
            super();
        }
    };

    export class ForallType extends BaseType {
        public id: () => string;
        public inner: () => Type;
        public bound: () => Type;

        constructor(
            id: string,
            inner: Type,
            bound: Type) {
            super();

            this.id = function() { return id; }
            this.inner = function() { return inner; }
            this.bound = function() { return bound; }
        }
    };

    export class ExistsType extends BaseType {
        public id: () => string;
        public inner: () => Type;
        public bound: () => Type;

        constructor(
            id: string,
            inner: Type,
            bound: Type) {
            super();

            this.id = function() { return id; }
            this.inner = function() { return inner; }
            this.bound = function() { return bound; }
        }
    };

    export class RecordType extends BaseType {
        public add: (id: string, type: Type) => boolean;
        public select: (id: string) => Type;
        public isEmpty: () => boolean;
        public fields: () => Object;
        public length: () => number;

        constructor() {
            super();

            let fields = {};
            this.add = function(id, type) {
                if (fields.hasOwnProperty(id)) {
                    return false;
                }
                fields[id] = type;
                return true;
            };
            this.select = function(id) {
                return fields[id];
            };
            this.isEmpty = function() {
                return Object.keys(fields).length === 0;
            };
            // note: assumes no one will attempt to change the map
            this.fields = function() {
                return fields;
            };

            this.length = function() {
                return Object.keys(fields).length;
            };
        }
    };

    export class NoneType extends BaseType {
        constructor() {
            super();
            // intentionally empty
        }
    };

    export class TopType extends BaseType {
        constructor() {
            super();
            // intentionally empty
        }
    };

    export class ReferenceType extends BaseType {
        public location: () => Type;
        constructor(location: Type) {
            super();
            // intentionally empty
            this.location = function() { return location; }
        }
    };

    export class StackedType extends BaseType {
        public left: () => Type;
        public right: () => Type;
        constructor(left: Type, right: Type) {
            super();
            // intentionally empty
            this.left = function() { return left; }
            this.right = function() { return right; }
        }
    };

    export class CapabilityType extends BaseType {
        public location: () => Type;
        public value: () => Type;
        constructor(loc: Type, val: Type) {
            super();
            // intentionally empty
            this.location = function() { return loc; }
            this.value = function() { return val; }
        }
    };

    export class LocationVariable extends BaseType {
        public index: () => number;
        public name: () => string;
        public bound: () => Type;
        public copy: (number) => LocationVariable;
        constructor(name: string, index: number, bound?: Type) {
            super();
            this.index = function() { return index; }
            this.name = function() { return name; }
            this.bound = function() { return bound; }
            this.copy = function(j: number) { return new LocationVariable(name, j, bound); }
        }
    };

    export class TypeVariable extends BaseType {
        public index: () => number;
        public name: () => string;
        public bound: () => Type;
        public copy: (number) => TypeVariable;
        constructor(name: string, index: number, bound?: Type) {
            super();
            this.index = function() { return index; }
            this.name = function() { return name; }
            this.bound = function() { return bound; }
            this.copy = function(j: number) { return new TypeVariable(name, j, bound); }
        }
    };

    export class PrimitiveType extends BaseType {
        public name: () => string;
        constructor(name: string) {
            super();
            this.name = function() { return name; }
        }
    };

    export class RelyType extends BaseType {
        public rely: () => Type;
        public guarantee: () => Type;
        constructor(rely: Type, guarantee: Type) {
            super();
            this.rely = function() { return rely; }
            this.guarantee = function() { return guarantee; }
        }
    };

    export class GuaranteeType extends BaseType {
        public rely: () => Type;
        public guarantee: () => Type;
        constructor(guarantee: Type, rely: Type) {
            super();
            this.rely = function() { return rely; }
            this.guarantee = function() { return guarantee; }
        }
    };

    export class DefinitionType extends BaseType {
        public definition: () => string;
        public args: () => Type[];
        public getDefinition: () => Type;
        public getParams: () => Type[];
        public getTypeDef: () => any;

        constructor(definition_name, arg, typedef) {
            super();
            this.definition = function() { return definition_name; }
            this.args = function() { return arg; }
            // these fetch from the typedef map
            this.getDefinition = function() {
                return typedef.getDefinition(definition_name);
            }
            this.getParams = function() {
                return typedef.getType(definition_name);
            }
            this.getTypeDef = function() {
                return typedef;
            }
        }
    };

    unsafe_addNewType(FunctionType);
    unsafe_addNewType(BangType);
    unsafe_addNewType(SumType);
    unsafe_addNewType(StarType);
    unsafe_addNewType(AlternativeType);
    unsafe_addNewType(IntersectionType);
    unsafe_addNewType(TupleType);
    unsafe_addNewType(ForallType);
    unsafe_addNewType(ExistsType);
    unsafe_addNewType(RecordType);
    unsafe_addNewType(NoneType);
    unsafe_addNewType(TopType);
    unsafe_addNewType(ReferenceType);
    unsafe_addNewType(StackedType);
    unsafe_addNewType(CapabilityType);
    unsafe_addNewType(LocationVariable);
    unsafe_addNewType(TypeVariable);
    unsafe_addNewType(PrimitiveType);
    unsafe_addNewType(RelyType);
    unsafe_addNewType(GuaranteeType);
    unsafe_addNewType(DefinitionType);

    // append 'toString' method to types
    // toString( indexesOnly ) // undefined means false
    // if indexesOnly == true then it will only print variable's indexes, not their names.

    // defines which types get wrapping parenthesis
    function wrap(t, v) {
        if (t.type === types.ReferenceType ||
            t.type === types.FunctionType ||
            t.type === types.StackedType ||
            t.type === types.StarType ||
            t.type === types.AlternativeType ||
            t.type === types.SumType) {
            return '(' + t.toString(v) + ')';
        }
        return t.toString(v);
    };

    function setupToString(type) {
        switch (type) {

            case types.FunctionType:
                return function(v) {
                    return wrap(this.argument(), v) + " -o " + wrap(this.body(), v);
                };

            case types.BangType:
                return function(v) {
                    return "!" + wrap(this.inner(), v);
                };

            case types.RelyType:
                return function(v) {
                    return wrap(this.rely(), v) + ' => ' + wrap(this.guarantee(), v);
                };

            case types.GuaranteeType:
                return function(v) {
                    return wrap(this.guarantee(), v) + ' ; ' + wrap(this.rely(), v);
                };

            case types.SumType:
                return function(v) {
                    var tags = this.tags();
                    var res = [];
                    for (var i in tags) {
                        res.push(tags[i] + '#' + wrap(this.inner(tags[i]), v));
                    }
                    return res.join('+');
                };

            case types.StarType:
                return function(v) {
                    var inners = this.inner();
                    var res = [];
                    for (var i = 0; i < inners.length; ++i)
                        res.push(wrap(inners[i], v));
                    return res.join(' * ');
                };

            case types.AlternativeType:
                return function(v) {
                    var inners = this.inner();
                    var res = [];
                    for (var i = 0; i < inners.length; ++i)
                        res.push(wrap(inners[i], v));
                    return res.join(' (+) ');
                };

            case types.IntersectionType:
                return function(v) {
                    var inners = this.inner();
                    var res = [];
                    for (var i = 0; i < inners.length; ++i)
                        res.push(wrap(inners[i], v));
                    return res.join(' & ');
                };

            case types.ExistsType:
                return function(v) {
                    return 'exists' + (v ? '' : ' ' + this.id().name())
                        + (!this.bound() ? '' : '<:' + wrap(this.bound(), v))
                        + '.' + wrap(this.inner(), v);
                };

            case types.ForallType:
                return function(v) {
                    return 'forall' + (v ? '' : ' ' + this.id().name())
                        + (!this.bound() ? '' : '<:' + wrap(this.bound(), v))
                        + '.' + wrap(this.inner(), v);
                };

            case types.ReferenceType:
                return function(v) {
                    return "ref " + wrap(this.location(), v);
                };

            case types.CapabilityType:
                return function(v) {
                    return 'rw ' + wrap(this.location(), v) + ' ' + wrap(this.value(), v);
                };

            case types.StackedType:
                return function(v) {
                    return wrap(this.left(), v) + ' :: ' + wrap(this.right(), v);
                };

            case types.RecordType:
                return function(v) {
                    var res = [];
                    var fields = this.fields();
                    for (var i in fields)
                        res.push(i + ": " + wrap(fields[i], v));
                    return "[" + res.join() + "]";
                };

            case types.TupleType:
                return function(v) {
                    var res = [];
                    var fields = this.inner();
                    for (var i in fields)
                        res.push(wrap(fields[i], v));
                    return "[" + res.join() + "]";
                };

            case types.DefinitionType:
                return function(v) {
                    if (this.args().length > 0) {
                        var args = this.args();
                        var tmp = [];
                        for (var i = 0; i < args.length; ++i) {
                            tmp.push(wrap(args[i], v));
                        }
                        return wrap(this.definition(), v) + '[' + tmp.join() + ']';
                    }
                    return wrap(this.definition(), v);
                };

            case types.LocationVariable:
            case types.TypeVariable:
                return function(v) {
                    if (!v)
                        return this.name() + '^' + this.index();

                    var str = '';
                    // only add type bound if it is a TypeVariable
                    if (this.type === types.TypeVariable) {
                        var b = this.bound();
                        // with a valid bound
                        if (b !== null) {
                            // for clarity we use '$' instead of '<:'
                            str = '$' + b.toString(v);
                        }
                    }

                    return this.index() + str;
                };

            case types.PrimitiveType:
                return function(v) { return this.name(); };

            case types.NoneType:
                return function(v) { return 'none'; };

            case types.TopType:
                return function(v) { return 'top'; };

            default:
                error('@setupToString: Not expecting type: ' + type);
        }
    }

    // attach 'toString' to all types
    for (let i in types) {
        let t = types[i];
        let fun = setupToString(t);
        error(!fct[t].hasOwnProperty('toString') || ("Duplicated " + t));
        fct[t].prototype.toString = fun;
    }


	/**
	 * The typing environment is a spaghetti stack where the parent
	 * may be shared among several different typing environments.
	 * All methods return:
	 * 	undefined - new element collides with a previously existing one;
	 *  null/value - if all OK.
	 */
    export class Gamma {

        constructor(
            private typedef: TypeDefinition,
            private parent: Gamma,
            private id?: string,
            private type?: Type,
            private bound?: Type) {
        }
        // id, type, bound are left undefined when called with:
        // new Gamma( typedef, null );

        getTypeDef(): TypeDefinition {
            return this.typedef;
        }

        // scope methods
        newScope(id: string, type: Type, bound: Type) {
            return new Gamma(this.typedef, this, id, type, bound);
        }

        endScope() {
            return this.parent;
        }

        // getters
        getType(index: number): Type {
            if (index === 0)
                return this.type;
            if (this.parent === null || index < 0)
                return undefined;
            return this.parent.getType(index - 1);
        }
        getBound(index: number): Type {
            if (index === 0)
                return this.bound;
            if (this.parent === null || index < 0)
                return undefined;
            return this.parent.getBound(index - 1);
        }
        getTypeByName(name: string): Type {
            if (name === this.id)
                return this.type;
            if (this.parent === null)
                return undefined;
            return this.parent.getTypeByName(name);
        }

        // returns the depth of 'name' in the spaghetti stack.
        // return: starts at 0, -1 if not found.
        getNameIndex(name: string): number {
            if (this.id === name) {
                return 0;
            }
            if (this.parent === null)
                return -1; // not found

            var tmp = this.parent.getNameIndex(name);
            if (tmp === -1)
                return tmp;
            return 1 + tmp;
        }

        forEach(f: (index: number, name: string, type: Type, bound: Type) => void, i?: number) {
            if (i === undefined)
                i = 0;

            f(i, this.id, this.type, this.bound);

            if (this.parent !== null)
                this.parent.forEach(f, i + 1);
        }

    };

    export class TypeDefinition {

        // map definition's name with its body
        private typedefs: { [s: string]: Type };

        // maps deinition's name with its arguments
        private typedefs_args: { [s: string]: Type[] };

        constructor() {
            this.reset();
        }

        addType(name: string, args: Type[]) {
            if (this.typedefs_args.hasOwnProperty(name))
                return false;
            this.typedefs_args[name] = args;
            return true;
        }

        addDefinition(name: string, definition: Type) {
            if (this.typedefs.hasOwnProperty(name))
                return false;
            this.typedefs[name] = definition;
            return true;
        }
        getType(name: string): Type[] {
            return this.typedefs_args[name];
        }

        getDefinition(name: string): Type {
            return this.typedefs[name];
        }

        reset() {
            this.typedefs = {};
            this.typedefs_args = {};
        }

    };

};
