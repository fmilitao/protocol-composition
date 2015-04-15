// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

// FIXME: this is actually a class??
function ErrorWrapper(msg, kind, ast, debug, stack?) {
    this.message = msg;
    this.kind = kind;
    this.ast = ast;
    this.debug = debug;
    this.stack = stack || (<any>(new Error())).stack.toString();
    this.toString = function() {
        return this.kind + ': ' + this.message;
    }
};

// convenient assert function to wrap errors
function assertF(kind, f, msg, ast) {
    let result = undefined;
    let error = true; // because exceptions
    let debug = null;
    try {
        if (f instanceof Function) {
            result = f();
            error = result === undefined;
        }
        else {
            result = f;
            error = result === undefined || result === false;
        }
    } catch (e) {
        // if it is already one of our own exceptions don't wrap
        if (e instanceof ErrorWrapper)
            throw e;
        if (e instanceof RangeError)
            msg = e.message;
        debug = (e || e.message);
    }
    if (error)
        throw new ErrorWrapper(msg, kind, ast, debug);
    return result;
};


module AST {

    function merge(kind, l, r) {
        let tmp = [];
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
    };

    function unsafe_addKind(obj) {
        obj.prototype['kind'] = obj.name;
    };

    // convenient but hacky class for adding a match to both Exp and Types
				class BaseAST {

        public line: number;
        public col: number;
        public last_line: number;
        public last_col: number;

        public kind: string; // attached (statically) by 'unsafe_addKind'

        constructor(info?) {
												// next was found through the link:
												// http://www.gnu.org/software/bison/manual/html_node/Actions-and-Locations.html#Actions-and-Locations
            if (info) {
                // Jison lines start at line 1, but ACE indexing starts at 0
                this.line = info.first_line - 1;
                this.col = info.first_column;
                this.last_line = info.last_line - 1;
                this.last_col = info.last_column;
            }
        }

        match<T>(cases: any): T {

            // for debugging:
            if (!cases.hasOwnProperty(this.kind))
                throw new Error('Missing: ' + this.kind + ' on ' + cases.constructor.name);

            // unsafe, but convenient way to do pattern matching within typescript
            // while avoiding copy pasting over all classes that need this.
            return cases[this.kind](<any>this);
        }


    };

    //
    // Expressions
    //

    export module Exp {

        export interface Exp {
            match<T>(m: MatchExp<T>): T;
        };

        export interface MatchExp<T> {
												TypeDef(x: TypeDef): T;
												Program(x: Program): T;
												Share(x: Share): T;
												Subtype(x: Subtype): T;
												Equals(x: Equals): T;
            Forall(x: Forall): T;
        };

								export class TypeDef extends BaseAST {
            constructor(
                public id: Exp,
                public type: Exp,
                public pars: Exp[],
                info: any
                ) {
                super(info);
            }
								};

								export class Program extends BaseAST {
												constructor(
																public typedefs: TypeDef[],
																public exp: Exp[],
																info: any
																) {
																super(info);
												}
								};


								export class Share extends BaseAST {
            constructor(
                public value: boolean,
                public type: Type.Type,
                public a: Type.Type,
                public b: Type.Type,
                info: any
                ) {
                super(info);
            }
								};

								export class Subtype extends BaseAST {
            constructor(
                public value: Exp,
                public a: Type.Type,
                public b: Type.Type,
                info: any
                ) {
                super(info);
            }
								};

								export class Equals extends BaseAST {
            constructor(
                public value: Exp,
                public a: Type.Type,
                public b: Type.Type,
                info: any
                ) {
                super(info);
            }
								};

        export class Forall extends BaseAST {
												constructor(
																public id: string,
																public exp: Exp,
																public bound: Type.Type,
																info: any
																) {
																super(info);
												}
								};

        // adds static 'kind' information to each class
        unsafe_addKind(TypeDef);
        unsafe_addKind(Program);
        unsafe_addKind(Share);
        unsafe_addKind(Subtype);
        unsafe_addKind(Equals);
        unsafe_addKind(Forall);

				};

				//
				// Types
				//

    export module Type {

        export interface Type {
            match<T>(m: MatchType<T>): T;
        };

        export interface MatchType<T> {
            Substitution(x: Substitution): T;

            Exists(x: Exists): T;
												Forall(x: Forall): T;
												Stacked(x: Stacked): T;
												Rely(x: Rely): T;
												Guarantee(x: Guarantee): T;
												Sum(x: Sum): T;
												Star(x: Star): T;
												Alternative(x: Alternative): T;
												Intersection(x: Intersection): T;
												Function(x: Function): T;
            Capability(x: Capability): T;
            Name(x: Name): T;
            Primitive(x: Primitive): T;
            Reference(x: Reference): T;
            Bang(x: Bang): T;
            Record(x: Record): T;
            Field(x: Field): T;
            Tuple(x: Tuple): T;
            Tagged(x: Tagged);
            None(x: None): T;
            Top(x: Top): T;
            Definition(x: Definition): T;

        };

        export class Substitution extends BaseAST {
            constructor(
                public type: Type,
                public to: Type,
                public from: Type,
                info: any
                ) {
                super(info);
            }
        };

								export class Exists extends BaseAST {
												constructor(
																public id: string,
																public exp: Type,
																public bound: Type,
																info: any
																) {
																super(info);
												}
								};

								export class Forall extends BaseAST {
												constructor(
																public id: string,
																public exp: Type,
																public bound: Type,
																info: any
																) {
																super(info);
												}
								};

								export class Stacked extends BaseAST {
												constructor(
																public left: Type,
																public right: Type,
																info: any
																) {
																super(info);
												}
								};

								export class Rely extends BaseAST {
												constructor(
																public left: Type,
																public right: Type,
																info: any
																) {
																super(info);
												}
								};

								export class Guarantee extends BaseAST {
												constructor(
																public left: Type,
																public right: Type,
																info: any
																) {
																super(info);
												}
								};

								export class Sum extends BaseAST {
												constructor(
																public sums: Tagged[],
																info: any
																) {
																super(info);
												}
								};

								export class Star extends BaseAST {
            public types: Type[];
												constructor(
																left: Type,
																right: Type,
																info: any
																) {
																super(info);
																this.types = merge(this.kind, left, right);
												}
								};

								export class Intersection extends BaseAST {
            public types: Type[];
												constructor(
																left: Type,
																right: Type,
																info: any
																) {
																super(info);
																this.types = merge(this.kind, left, right);
												}
								};

								export class Alternative extends BaseAST {
            public types: Type[];
												constructor(
																left: Type,
																right: Type,
																info: any
																) {
																super(info);
																this.types = merge(this.kind, left, right);
												}
								};

								export class Function extends BaseAST {
												constructor(
																public arg: Type,
																public exp: Type,
																info: any
																) {
																super(info);
												}
								};

								export class Capability extends BaseAST {
												constructor(
																public id: Type,
																public type: Type,
																info: any
																) {
																super(info);
												}
								};

								export class Name extends BaseAST {
												constructor(
																public text: string,
																info: any
																) {
																super(info);
												}
								};

								export class Primitive extends BaseAST {
												constructor(
																public text: string,
																info: any
																) {
																super(info);
												}
								};

								export class Reference extends BaseAST {
												constructor(
																public text: string,
																info: any
																) {
																super(info);
												}
								};

								export class Bang extends BaseAST {
												constructor(
																public type: Type,
																info: any
																) {
																super(info);
												}
								};

								export class Record extends BaseAST {
												constructor(
																public exp: Field[],
																info: any
																) {
																super(info);
												}
								};

								export class Field extends BaseAST {
												constructor(
                public id: string,
																public exp: Type,
																info: any
																) {
																super(info);
												}
								};

								export class Tuple extends BaseAST {
												constructor(
																public exp: Type[],
																info: any
																) {
																super(info);
												}
								};

								export class Tagged extends BaseAST {
												constructor(
																public tag: string,
																public exp: Type,
																info: any
																) {
																super(info);
												}
								};

								export class None extends BaseAST {
												constructor(info: any) {
																super(info);
												}
								};

								export class Top extends BaseAST {
												constructor(info: any) {
																super(info);
												}
								};

								export class Definition extends BaseAST {
												constructor(
                public name: string,
                public args: Type[],
                info: any
                ) {
																super(info);
												}
								};

        // adds static 'kind' information to each class
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

				};

};
