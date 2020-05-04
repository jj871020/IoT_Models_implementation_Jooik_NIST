typeside T = literal { 
	java_types
		String = "java.lang.String"
		Int = "java.lang.Integer"
		List = "com.google.common.collect.ImmutableList"
		Bool = "java.lang.Boolean"
		Fn = "jdk.nashorn.api.scripting.JSObject"
		BinFn = "jdk.nashorn.api.scripting.JSObject"

	java_constants
		String = "return input[0]"
		Int = "return java.lang.Integer.parseInt(input[0])"
		List = "throw new RuntimeException()"
		Bool = "java.lang.Boolean.parseBoolean(input[0])"
		Fn = "throw new RuntimeException()"
		BinFn = "throw new RuntimeException()"

	java_functions
		true : -> Bool = "return true"
		plus : Int,Int-> Int = "return (input[0] + input[1]).intValue()"
		nil : -> List = "return com.google.common.collect.ImmutableList.of()"						// works
		asList : Int -> List = "return com.google.common.collect.ImmutableList.of(input[0])"			// works
//		cons : List, Int -> List = "return input[0].add(input[1])"			// doesn't
		concat : List, List -> List = "return com.google.common.collect.ImmutableList.of(input[0],input[1])"	// doesn't
		lessThan : Int, Int -> Bool = "return (input[0]<input[1])"
		and	: Bool, Bool -> Bool = "return (input[0] && input[1])"
		parse : String -> Fn = "return new javax.script.ScriptEngineManager().getEngineByName(\"nashorn\").eval(input[0])"
		//binary function
		parse2 : String -> BinFn = "return new javax.script.ScriptEngineManager().getEngineByName(\"nashorn\").eval(input[0])"
		apply : Fn, Int -> Int = "return java.lang.Integer.parseInt(0+input[0].call(input[0],input[1]))"
		apply2 : BinFn, Int, String -> Int = "return java.lang.Integer.parseInt(input[0].call(input[0],input[1],input[2]))"
		onUpdate: Int -> Int = "return java.lang.Integer.parseInt(5 + input[0])"		// instead of having these two 
		offUpdate: Int -> Int = "return java.lang.Integer.parseInt(-4 + input[0])"	// separately...
// a function taking two integers and spitting out 0 or 1 (in the constraints we will have conditional statement)
}
// states should have a list of nubmers (work on this)

schema S = literal : T {
	entities
		Timestep Mode
	foreign_keys
		mode : Timestep -> Mode
	attributes
		time : Timestep -> Int
		state : Timestep -> Int   // will be a list of values of envVars
		cmnd: Timestep -> String
		modeName : Mode-> String
//		update : Mode -> Fn					////////////////////////////////// commented out
	observation_equations
	options
		allow_java_eqs_unsafe = true
}


constraints advance = literal : S {
	// Key for Mode
	forall m1 m2:Mode
	where m1.modeName = m2.modeName
	-> where m1 = m2

	// Control algorithm
	forall t:Timestep
	where lessThan(t.state,5)=true
	->
	where t.cmnd = "on"

	forall t:Timestep
	where lessThan(10,t.state)=true
	->
	where t.cmnd = "off"

	forall t:Timestep
	where 
		lessThan(4,t.state)=true
		lessThan(t.state,11)=true
	->
	where t.cmnd = t.mode.modeName
	
	// Next timestep

	forall t:Timestep
	where lessThan(t.time,10)=true
		t.cmnd = "on"							////////////////////////////////    added
	->
	exists tt:Timestep
	where
		tt.time = plus(1,t.time)
		tt.state = onUpdate(t.state)
//		tt.state = apply(tt.mode.update,t.state)			///////////////////////////// commented out
		tt.mode.modeName = t.cmnd

	forall t:Timestep										////////////////////////////////
	where lessThan(t.time,10)=true							//  added
		t.cmnd = "off"		
	->
	exists tt:Timestep
	where
		tt.time = plus(1,t.time)
		tt.state = offUpdate(t.state)
//		tt.state = apply(tt.mode.update,t.state)
		tt.mode.modeName = t.cmnd							///////////////////////////////////// 

}


instance I = literal : S {
	generators
		t0: Timestep
		m1 m2 : Mode
	equations
		t0.time = 0
		t0.state = 2
		t0.mode = m1
		m1.modeName = "on"
//		m1.update = parse("function (s) {return s+5}")					////////////////// commented out
		m2.modeName = "off"
//		m2.update = parse("function (s) {return s-3}")					/////////////////// commented out
}


instance J = chase advance I {
	options
		allow_java_eqs_unsafe = true
		require_consistency = false
		timeout = 100
}
