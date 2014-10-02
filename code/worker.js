// Copyright (C) 2013 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

//
// Worker thread
//

var isWorker = typeof(window) === 'undefined';

// only loads the following if it is a standalone thread
if( isWorker ){

	// convenient debug
	var console = function(){
		var aux = function(k,arg){
			var tmp =[];
			for( var i=0; i<arg.length; ++i )
				tmp.push( arg[i].toString() );
			self.postMessage({kind: k, data: '[Worker] '+tmp.join(' ') });
		}
		
		return {
			log : function(){ aux('log',arguments) },
			error : function(){ aux('error',arguments) },
			debug  : function(){ aux('debug',arguments) }
		};
	}();

	// libs
	importScripts('../lib/jison.js');
	importScripts('parser.js','interpreter.js','typechecker.js');

}

var parser = Parser( (isWorker?'':'code/') + 'grammar.jison' );
var interpreter = function(ast){ return Interpreter.run(ast,libLoader); };
var types = TypeChecker.types;
var checker = TypeChecker.check;

//
// Send function
//

var send;
if( isWorker ){
	send = function(k,msg){
		self.postMessage({kind: k, data: msg });
	};
	
	self.addEventListener('message', function(e) {
		var m = e.data;
		try{
			// this is the 'receiver' var from below
			receiver[m.kind](m.data);
		}catch(e){
			console.error(e);
		}
	}, false);
} else {
	// Just for local debugging, MAIN_HANDLER is global var
	send = function(kind,data) {
		try{
			MAIN_HANDLER[kind](data);
		} catch(e) {
			console.error(e);
		}
	};
}

//
// Receiver object
//

var receiver = new function(){
	
	// local state between calls
	// to avoid reparsing, the 'ast' is made available
	// to the other listener functions through this var.
	var ast = null;
	var typeinfo = null;
	var autorun = true;
	
	var handleError = function(e){
		if( e.stack )
			console.error( e.stack.toString() );
		send('errorHandler', JSON.stringify(e));
	};
	
	this.EVAL = function(data){
		try{
			ast = null;
			typeinfo = {};
			send('clearAll',null);
	
			ast = parser( data );

			send('println', '<b>Type</b>: '+
				toHTML( checker( ast , typeinfo, libTyper ) ) );

			if( !isWorker ){
				// some debug information
				console.debug( 'checked in: '+typeinfo.diff+' ms' );
			}

			if( autorun ){
				send('println', '<b>Result</b>: '+
					interpreter( ast,
						function(msg){ send('println',msg.toString()) } ) );
			}
			
			// no errors!
			send('updateAnnotations', null);
		}catch(e){
			handleError(e);
		}
	};
	
	this.AUTO = function(auto){
		try{
			autorun = auto;
			if( autorun && ast !== null ){
				send('println', "<b>FORCED RUN - Result:</b> "+
					interpreter( ast,
						function(msg){ send('println',msg.toString()) } ) );
			}
		}catch(e){
			handleError(e);
		}
	};
	
	this.CHECKER = function(pos){
		try{
			// only if parsed correctly
		   	if( ast === null || typeinfo === null )
		   		return;
		   	else{
		   		// resets typing output
		   		send('clearTyping',null);
		   	}
		    
			send('printTyping',info(typeinfo,pos).toString());
		}catch(e){
			handleError(e);
		}
	};
	
};

if( !isWorker ){
	// intentional GLOBAL variable
	var WORKER_HANDLER = receiver;
}

//
// Quick and Dirty Standard Lib for basic arithm.
//

var libLoader = function( file, ctx ){
	var v = ctx.factory;

	// println: forall T.( T -o T )
	if( file === 'println' ){
		var println = new v.Function();
		println.call = function(msg){
			send('println',msg.toString());
			return msg;
		};
		return println;
	}
	
	// add: int -o int -o !int
	if( file === 'add' ){	
		var add = new v.Function();
		add.call = function(msg){
			var tmp = new v.Function();
			tmp.call = function(arg){ return msg+arg; }
			return tmp;
		};
		return add;
	}
	
	// concat: int -o int -o !int
	if( file === 'concat' ){	
		var add = new v.Function();
		add.call = function(msg){
			var tmp = new v.Function();
			tmp.call = function(arg){ return msg+arg; }
			return tmp;
		};
		return add;
	}
	
	if( file === 'abort' ){
		var abort = new v.Function();
		abort.call = function(msg){
			//FIXME this is not clean, using RangeError just like stack overflow
			// error is considerer a horrible hack and you should be ashamed.
			throw new RangeError(msg);
		};
		return abort;
	}
	
	// others are unknown
	return undefined;
};

var libTyper = function( file, ctx ){
	var v = ctx.factory;

	// println: !(forall T.( T -o T ))
	if( file === 'println' ){
		return new v.BangType(
			new v.ForallType(
				new v.TypeVariable('T'),
				new v.FunctionType(
					new v.TypeVariable('T'),
					new v.TypeVariable('T') 
					)
			) 
		);
	}
		
	// add: !(int -o int -o !int)
	if( file === 'add' ){
		return new v.BangType(
			new v.FunctionType(
				new v.PrimitiveType('int'),
				new v.FunctionType(
					new v.PrimitiveType('int'),
					new v.BangType(new v.PrimitiveType('int'))
					) 
			)
		);
	}
	
	// concat: !(string -o string -o !string)
	if( file === 'concat' ){
		return new v.BangType(
			new v.FunctionType(
				new v.PrimitiveType('string'),
				new v.FunctionType(
					new v.PrimitiveType('string'),
					new v.BangType(new v.PrimitiveType('string'))
					) 
			)
		);
	}
	
	if( file === 'abort' ){
		return new v.BangType(
			new v.ForallType(
				new v.TypeVariable('T'),
				new v.FunctionType(
					new v.StackedType(
						new v.PrimitiveType('string'),
						new v.TypeVariable('T')
						),
					new v.BangType(new v.RecordType())
				)
			)
		);
	}
	
	// others are unknown
	return undefined;
};

//
// Printing Type Information
//

var printAST = function(ast,r){
	return "@"+(ast.line+1)+":"+ast.col+'-'
		+(ast.last_line+1)+':'+ast.last_col+' '+ast.kind;
		//+'\nType: '+toHTML(r) // Too much to also show resulting type.
}

var printConformance = function(cf){
	var has3 = (cf[0][3] !== undefined);
	var tmp = '<table class="typing_conformance"><tr><th>State</th>'+
		'<th>P0</th><th>P1</th>'+
		( has3 ? '<th>P2</th>': '')+
		'</tr>';
	for(var i=0;i<cf.length;++i){
		tmp+= '<tr>'+
			'<td>'+ toHTML(cf[i][0]) +'</td>'+ 
			'<td>'+ toHTML(cf[i][1]) +'</td>'+
			'<td>'+ toHTML(cf[i][2]) +'</td>'+
			( has3 ? ('<td>'+ toHTML(cf[i][3]) +'</td>') : '')+ 
			'</tr>';
	}
	return tmp+'</table>';
}

var printEnvironment = function(env){
	var res = _printEnvironment(env);
	
	var gamma = res.gamma;
	var delta = res.delta;
	
	gamma.sort(); // to ensure always the same order
	gamma = gamma.join(',\n    ');
	
	delta.sort(); // ...same order
	delta = delta.join(',\n    ');
	
	return "\u0393 = "+gamma+"\n"+"\u0394 = "+delta;
}

var _printEnvironment = function(env){
	var gamma = [];
	var delta = [];
	var visited = [];
	
	env.visit( true, // visit all elements 
	function(id,val,isCap,isType){
		// if duplicated do not print, this may happen due to
		// stack of environments for names (i.e. non type/loc vars).
		if( visited.indexOf(id) !== -1 )
			return;
		
		if( isCap ){
			delta.push( toHTML(val) );
			return;
		}
		
		// only non-caps may not be repeated, since caps have null 'id'
		visited.push(id);
		
		if( isType ){
			// is a type/location variable
			if( val.type === types.LocationVariable ){
				gamma.push('<span class="type_location">'+val.name()+'</span>: <b>loc</b>');
				return;
			}
			if( val.type === types.TypeVariable ){
				gamma.push('<span class="type_variable">'+val.name()+'</span>: <b>type</b>');
				return;
			}
		}
		
		if( val.type === types.BangType ){
			gamma.push('<span class="type_name">'+id+'</span>'+": "+toHTML(val.inner()));
			return;
		}			
		delta.push('<span class="type_name">'+id+'</span>'+": "+toHTML(val));
	});

	var e = env;
	while( e !== null ){
		if( e.$defocus_guarantee !== null ){
			var tmp = _printEnvironment(e.$defocus_env).delta;
			if( tmp.length > 0 ){
				tmp.sort(); // ...same order
				tmp = tmp.join(', ');
			}else{
				tmp = '&#8709;';
			}
			delta.push( toHTML(e.$defocus_guarantee) +wq( wQ(' &#9659; ')+wq(tmp) ) );
			break;
		}
		e = e.$parent;
	}
	
	return { delta : delta, gamma : gamma };
}


var info = function(tp,pos){
	var type_info = tp.info;
	var diff = tp.diff;
	var ptr = null;
	var indexes = [];
					
	// search for closest one
	for( var i in type_info ){
		var ast = type_info[i].ast;
		if( ptr === null ){
			ptr = i;
			indexes = [i];
		} else {
			var old = type_info[ptr].ast;
			
			var dy = Math.abs(ast.line-pos.row);							
			var _dy = Math.abs(old.line-pos.row);
			
			if( dy < _dy ){
				// if closer, pick new one
				ptr = i;
				indexes = [i];
				continue;
			}
			
			// on same line
			if( dy === _dy ){
				var dx = Math.abs(ast.col-pos.column);
				var _dx = Math.abs(old.col-pos.column);
					
				// if closer, pick new one
				if( dx < _dx ){
					ptr = i;
					indexes = [i];
					continue;
				}else{
					if( dx === _dx ){
						// one more
						indexes.push(i);
						continue;
					}	
				}
			}
		}
		/*
		if( ( ast.line < pos.row || 
	 		( ast.line === pos.row &&
				ast.col <= pos.column ) ) ){
	 			ptr = i;
	 	}*/
	}
	
	if( ptr === null || indexes.length === 0 )
		return '';

	var msg = '<b title="click to hide">Type Information</b> ('+diff+'ms)';
	//msg += "<hr class='type_hr'/>";
	
	var res = [];
	
	for(var i=0;i<indexes.length;++i){
		var ptr = indexes[i];
		// minor trick: only print if the same kind since alternatives
		// are always over the same kind...
		// IMPROVE: is there a better way to display this information?
		/* if( type_info[ptr].ast.kind !==
			type_info[indexes[0]].ast.kind )
			continue;*/
		var as = printAST( type_info[ptr].ast, type_info[ptr].res );
		var ev = printEnvironment( type_info[ptr].env );
		var cf = type_info[ptr].conformance;
		cf = (cf!==undefined?printConformance(cf):'');
	
		// group all those that have the same environment	
		var seen = false;
		for(var j=0;!seen && j<res.length;++j){
			var jj = res[j];
			if( jj.env === ev ){
				// already seen
				jj.ast += '<br/>'+as;
				if( jj.cf === '' )
					jj.cf += cf; // in case there is more than 1 conformance
				seen = true;
				break;
			}
		}
		
		if( !seen ){
			res.push( { ast : as, env : ev, cf : cf } );
		}
	}

	for(var i=0;i<res.length;++i){
		var tmp = res[i];
		msg += "<hr class='type_hr'/>"
			+ tmp.ast 
			+'<br/>'
			+ tmp.env
			+ tmp.cf;		
	}
	
	return msg;
}

//
// Convert type to HTML
//

// defines which types get wrapping parenthesis
var _toHTML = function(t){
	if( t.type === types.ReferenceType ||
		t.type === types.FunctionType ||
		t.type === types.StackedType ||
		t.type === types.StarType || 
		t.type === types.AlternativeType ||
		t.type === types.IntersectionType ||
		t.type === types.SumType ){
			return '('+toHTML(t)+')';
		}
	return toHTML(t);
}

var wq = function(t){ return '<span class="q">'+t+'</span>'; } // changer
var wQ = function(t){ return '<span class="Q">'+t+'</span>'; } // trigger

var toHTML = function (t){
	switch ( t.type ){
		case types.FunctionType:
			return wq( 
				wq( _toHTML(t.argument()) ) +
				wQ( ' &#x22b8; ' ) +
				//wQ( '<span class="type_fun"> &#x22b8; </span>' ) +
				wq( _toHTML(t.body()) )
				);
		case types.BangType:{
			var inner = t.inner();	
			return wq( wQ("!") + wq(_toHTML(t.inner())) );
		}
		case types.SumType:{
			var tags = t.tags();
			var res = [];
			for( var i in tags ){
				res.push(
					wQ( '<span class="type_tag">'+tags[i]+'</span>#' )+
					wq( _toHTML(t.inner(tags[i])) )
				); 
			}	
			return wq( res.join('+') );
		}
		case types.StarType:{
			var inners = t.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( wq( _toHTML( inners[i] ) ) ); 
			return wq( res.join( wQ(' * ') ) );
		}
		case types.IntersectionType:{
			var inners = t.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( wq( _toHTML( inners[i] ) ) ); 
			return wq( res.join( wQ(' &amp; ') ) );
		}
		case types.AlternativeType:{
			var inners = t.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( wq( _toHTML( inners[i] ) ) ); 
			return wq( res.join( wQ(' &#8853; ') ) );
		}
		case types.RecursiveType:
			return '<b>rec</b> '+
			( t.id().type === types.LocationVariable ?
				'<span class="type_location">' :
				'<span class="type_variable">')
			+t.id().name()+'</span>.'+_toHTML(t.inner());
		case types.ExistsType:
			return '&#8707;'+
			( t.id().type === types.LocationVariable ?
				'<span class="type_location">' :
				'<span class="type_variable">')
			+t.id().name()+'</span>.'+_toHTML(t.inner());
		case types.ForallType:
			return '&#8704;'+
			( t.id().type === types.LocationVariable ?
				'<span class="type_location">' :
				'<span class="type_variable">')
			+t.id().name()+'</span>.'+_toHTML(t.inner());
		case types.ReferenceType:
			return "<b>ref</b> "+
			'<span class="type_location">'+t.location().name()+'</span>';
		case types.CapabilityType:
			return '<b>rw</b> '+
			'<span class="type_location">'+t.location().name()+'</span> '+
			toHTML(t.value());
		case types.StackedType:
			return wq( wq(toHTML(t.left())) + wQ(' :: ')+ wq(toHTML(t.right())) );
		case types.RecordType: {
			var res = [];
			var fields = t.getFields();
			for( var i in fields )
				res.push('<span class="type_field">'+i+'</span>: '+toHTML(fields[i]));
			return "["+res.join(', ')+"]";
		}
		case types.TupleType: {
			var res = [];
			var values = t.getValues();
			for( var i in values )
				res.push( toHTML(values[i]) );
			return "["+res.join(', ')+"]";
		}
		case types.LocationVariable:
			return '<span class="type_location">'+t.name()+'</span>';
		case types.TypeVariable:
			return '<span class="type_variable">'+t.name()+'</span>';
		case types.PrimitiveType:
			return '<b>'+t.name()+'</b>';
		case types.NoneType:
			return '<b>none</b>';
		
		case types.DefinitionType:{
			var t_def = '<span class="type_definition">'+t.definition()+'</span>';
			if( t.args().length === 0 )
				return wq( t_def );
			
			var res = [];
			var as = t.args();
			for( var i in as )
				res.push( toHTML(as[i]) );
			return wq( t_def+wQ('[')+res.join(', ')+wQ(']') );
		}
		
		case types.RelyType:
			return wq( wq( _toHTML(t.rely()) )+wQ(' &#8658; ') + wq(_toHTML(t.guarantee())) );
		case types.GuaranteeType:
			return wq( wq( _toHTML(t.guarantee()) )+wQ(' ; ') + wq(_toHTML(t.rely())) );
		default:
			console.error( "Error @toHTML: " +t.type );
			return null;
		}
};



