// Copyright (C) 2013 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/**
 * Notes:
 * 	- ignores all location/type abstractions (i.e. as if erased)
 * 
 * REQUIRED Global variables (all declared in parser.js):
 * 	- AST.kinds, for all AST case analysis needs.
 *  - assertf, for error handling/flagging.
 */
	
var Interpreter = (function( AST, assertF ){
	
	// stuff to be exported from this module to outside contexts	
	var exports = {};
	
	//
	// Values Factory
	//
	
	var fct = {
		Function :
			function( body, variable, parent ) {
				this.call = function( argument ) {
					var env = new Heap( parent );
					env.set( variable, argument );
					return run( body, env );
				}
				this.toString = function() {
					return "Function Value";
				}
			},

		Record :
			function() {
				var fields = {};
		
				this.add = function( id, value ) {
					if ( fields.hasOwnProperty(id) ){
						return undefined;
					}
					fields[id] = value;
					return null;
				}
				this.select = function( id ) {
					if (fields.hasOwnProperty(id)) {
						return fields[id];
					} else {
						return undefined;
					}
				}
				this.toString = function() {
					var res = [];
					for( var i in fields )
						res.push(i+"="+fields[i].toString());
					return "{"+res.join()+"}";
				}
			},
	
		Tuple :
			function( vals ){
				this.values = function(){
					return vals;
				}
				this.toString = function() {
					return '{'+vals.join()+'}';
				}
			},
	
		Tagged : 
			function( t, v ) {
				this.tag = function(){
					return t;
				}
				this.value = function(){
					return v;
				}
				this.toString = function() {
					return t+"#"+v.toString();
				}
			},

		Reference : 
			function( i ) {
				var cell = i;
		
				this.set = function( value ) {
					var old = cell;
					cell = value;
					return old;
				}
				this.get = function() {
					return cell;
				}
				this.free = function() {
					var old = cell;
					cell = undefined;
					this.set = undefined;
					this.get = undefined;
					this.toString = function() {
						return "Dead Cell";
					}
					return old;
				}
				this.toString = function() {
					return "Reference Cell";
				}
			}

	};
	
	exports.factory = fct;

	//
	// Utils
	//

	var Heap = function( parent ) {
		var map = {};
		
		this.newScope = function(){
			return new Heap(this);
		}
		this.endScope = function(){
			return parent;
		}
		this.set = function( id, value ){
			map[id] = value;
		}
		this.get = function( id ){
			if ( map.hasOwnProperty(id) ) {
				return map[id]; 
			}else{
				if( parent === null )
					return undefined;
				else
					return parent.get(id);
			}
		}
	}
	
	var assert = function( f, msg, ast ){
		return assertF("Execution error",f,msg,ast);
	}
	
	//
	// Visitor
	//
	
	/*
	 * By having an auxiliary object that stores a map to functions, we should
	 * avoid a big switch (sequential) case comparision.
	 * Using such switch also makes it easier to assign the visit function when
	 * multiple node kinds have the same function value.
	 */
	
	var setupAST = function( kind ){	
		switch( kind ) {
			case AST.kinds.OPEN:
			case AST.kinds.LET: 
				return function(ast,env) {
					var value = run(ast.val, env);
					var newEnv = env;
					if( ast.id !== null ){
						newEnv = env.newScope();
						newEnv.set(ast.id, value);
					}
					return run(ast.exp, newEnv);
				};
				
			case AST.kinds.ID:
				return function(ast,env) {
					return assert(function() {
						return env.get(ast.text);
					}, "Identifier \'" + ast.text + "\' not found", ast);
				};

			case AST.kinds.DEREF: 
				return function(ast,env) {
					var exp = run(ast.exp, env);
					return assert(function(){
						return exp.get();
					},"Invalid dereference",ast);
				};

			case AST.kinds.NEW: 
				return function(ast,env) {
					var exp = run(ast.exp, env);
					return new fct.Reference(exp);
				};
				
			case AST.kinds.ASSIGN: 
				return function(ast,env) {
					var lvalue = run(ast.lvalue, env);
					var value = run(ast.exp, env);
					return assert(function(){
						return lvalue.set(value);
					},"Invalid assign",ast.lvalue);
				};
				
			case AST.kinds.DELETE: 
				return function(ast,env) {
					var lvalue = run(ast.exp, env);
					return assert(function(){
						return lvalue.free();
					},"Invalid delete",ast.exp);
				};
				
			case AST.kinds.TAGGED: 
				return function(ast,env) {
					var exp = run(ast.exp, env);
					return new fct.Tagged(ast.tag,exp);
				};
				
			case AST.kinds.CASE: 
				return function(ast,env) {
					var val = run(ast.exp, env);
					var tag = assert(function(){
						return val.tag();
					},"Invalid case",ast.exp);
					var branch = undefined;
					for(var i=0;i<ast.branches.length;++i){
						if( ast.branches[i].tag === tag ){
							branch = ast.branches[i];
							break;
						}
					}
					assert( branch, "No matching branch for "+tag, ast );
					var newEnv = env.newScope();
					newEnv.set(branch.id,val.value());
					return run(branch.exp, newEnv);
				};
				
			case AST.kinds.FUN: 
				return function(ast,env) {
					if( ast.rec !== null ){ //recursive function
						var newEnv = env.newScope();
						var rec = new fct.Function(ast.exp, ast.parms.id,newEnv);
						newEnv.set(ast.rec,rec);
						return rec;
					}
					return new fct.Function(ast.exp, ast.parms.id,env);
				};
				
			case AST.kinds.CALL: 
				return function(ast,env) {
					var fun = run(ast.fun, env);
					var arg = run(ast.arg, env);
					return assert(function(){
						return fun.call(arg);
					},"Invalid call",ast.arg);
				};
				
			case AST.kinds.SELECT: 
				return function(ast,env) {
					var rec = run(ast.left, env);
					var id = ast.right;
					return assert(function() {
						return rec.select(id);
					}, "Invalid field \'" + id + "\' for record", ast);
				};
				
			case AST.kinds.RECORD: 
				return function(ast,env) {
					var rec = new fct.Record();
					for(var i=0; i < ast.exp.length; ++i) {
						var field = ast.exp[i];
						var id = field.id;
						var value = run(field.exp, env);
						assert(function() {
							return rec.add(id, value);
						}, "Duplicated field \'" + id + "\' in record", field);
					}
					return rec;
				};
				
			case AST.kinds.TUPLE: 
				return function(ast,env) {
					var values = [];
	  				for (var i=0; i < ast.exp.length; ++i) {
	    				values.push( run(ast.exp[i], env) );
	  				}
	  				return new fct.Tuple(values);
				};
				
			case AST.kinds.LET_TUPLE: 
				return function(ast,env) {
					var vals = run(ast.val, env);
					vals = assert(function(){
						return vals.values();
					},"Invalid tuple",ast.val);
					var ids = ast.ids;
					assert( ids.length === vals.length,"Tuple size mismatch",ast.val);
					var newEnv = env;
					newEnv = env.newScope();
					for (var i = 0; i < vals.length; ++i) {
						newEnv.set(ids[i], vals[i]);
	  				}
					return run(ast.exp, newEnv);
				};
			
			case AST.kinds.FOCUS:
			case AST.kinds.DEFOCUS:
			case AST.kinds.SHARE:
				return function(ast,env){
					return new fct.Record();
				};

			case AST.kinds.CAP_STACK:
			case AST.kinds.PACK:
			case AST.kinds.FORALL:
			case AST.kinds.TYPE_APP:
			case AST.kinds.USE:
				return function(ast,env){
					return run(ast.exp, env);
				};
			
			case AST.kinds.NUMBER:
			case AST.kinds.BOOLEAN:
			case AST.kinds.STRING:
				return function(ast,env){
					// DANGER: assumes parser properly filters to only 
					// allow (safe) primitive javascript types.
					return eval(ast.text);
				};
				
			// the default handler for the remaining nodes just fails
			default: 
				return function(ast,env) {
					assert(false,'Error @run, '+ast.kind,ast);
				};
		}
	};
	
	var visitor = {};
	// setup visitors
	for( var i in AST.kinds ){
		assert( !visitor.hasOwnProperty(i),'Error @visitor, duplication: '+i);
		// find witch function to call on each AST kind of node
		visitor[i] = setupAST(i);
	}
	
	//
	// Run
	//
	
	var run = function(ast,env){
		if( !visitor.hasOwnProperty( ast.kind ) ){
			assert(false,'Error @run, '+ast.kind,ast);
		}
		return (visitor[ast.kind])( ast, env );
	}
	
	exports.run = function( ast, loader ){
		assert( ast.kind === AST.kinds.PROGRAM, 'Error @run, '+ast.kind, ast );
		
		var heap = new Heap(null);
		// only needs to look at imports, not typedefs.
		
		if( ast.imports !== null ){
		 	// loader does not need to be provided, but all imports are errors	
			assert( loader !== undefined, 'Error @run, missing import loader', ast );
			var libs = ast.imports;
			for( var i=0; i<libs.length; ++i ){
				var lib = libs[i];
				var value = loader( lib.id, exports );
				assert( value, "Invalid import: "+lib.id, lib );
				heap.set( lib.id, value );
			}
		}
		return run( ast.exp, heap );
	};
	
	return exports;
})(AST,assertF); // required globals
