// implementation for SIGMETRICS paper

typeside Type = literal { 
	java_types
		String = "java.lang.String"
		Float = "java.lang.Double"
	java_constants
		String = "return input[0]"
		Float = "return 0.0 + java.lang.Double.parseDouble(input[0])"
	java_functions
		plus : Float,Float -> Float = "return (input[0] + input[1])"
}


// Environmental variable Schema
schema EnvVarSchema = literal : Type {
	entities
		EnvVar
	attributes
		envVarName : EnvVar -> String
}


// Component Schema
schema CompSchema = literal : Type {
	entities
		Comp
		Cmnd
		Mode
		Transition
		Action
		Time
		Addr
		Protocol
		Channel
	foreign_keys
		hasTime 	: Action -> Time
		invokes 	: Action -> Cmnd
		cmnd		: Transition -> Cmnd
		pre			: Transition -> Mode
		post		: Transition -> Mode
		compM		: Mode -> Comp
		compC 		: Cmnd -> Comp
		ofComp 		: Addr -> Comp
		addr1 		: Channel -> Addr
		addr2 		: Channel -> Addr
		protocol	: Addr -> Protocol
	attributes
		
	path_equations
		Transition.pre.compM = Transition.post.compM
		Channel.addr1.protocol = Channel.addr2.protocol
	observation_equations
		
}


// Constraints for CompSchema
constraints CompConst = literal : CompSchema {
	//describes epi (Addr --ofComp-->> Comp)
	forall c1 : Comp
	->
	exists add1 : Addr
	where add1.ofComp = c1
}


// Sensor schema
schema SensorSchema = literal : Type {
	imports 
		CompSchema
		EnvVarSchema
	entities
		Sensor
		Obsv
		Query
		EnvState
		ObsVar
	foreign_keys
		asCompS 	: Sensor -> Comp
		//invokes 	: Action -> Cmnd
		//compC 	: Cmnd -> Comp
		sensor 		: Obsv -> Sensor
		asCmnd 		: Obsv -> Cmnd
		asAction 	: Query -> Action
		invokesQ	: Query -> Obsv
		value 		: Query -> EnvState
		varE		: EnvState -> EnvVar
		varO		: Obsv -> EnvVar
		observes 	: Obsv -> ObsVar
		observesVar	: ObsVar -> EnvVar
	attributes
		sensorType : Sensor -> String
		sensorName : Sensor -> String
		sensorOpRange : Sensor -> Float
		sensorNoise : Sensor -> Float
		sensorResolution : Sensor -> Float
		sensorAccuracy : Sensor -> Float
		sensorOutputRate : Sensor -> Float
		sensorPowerConsume : Sensor -> Float
		
	path_equations
		Query.value.varE = Query.invokes.varO
		Obsv.sensor.asCompS = Obsv.asCmnd.compC
	observation_equations
		
}


// Mapping from EnvVar schema to Sensor schema
mapping EnvVar2Sensor = literal : EnvVarSchema -> SensorSchema {
	imports identity EnvVarSchema
}


// Mapping from Comp schema to Sensor schema
mapping Comp2Sensor = literal : CompSchema -> SensorSchema {
	imports identity CompSchema
}


// Constraints for SensorSchema
constraints SensorConst = literal : SensorSchema {
	//describes monic (Sensor >--asComp--> Comp)
	forall s1 s2 : Sensor 
	where s1.asComp = s2.asComp
	-> 
	where s1 = s2

	//describes monic (Obsv >--asCmnd--> Cmnd)
	forall ob2 ob3 : Obsv
	where ob2.asCmnd = ob3.asCmnd
	->
	where ob2 = ob3

	//describes monic (Query >--asAction--> Action)
	forall q1 q2 : Query
	where q1.asAction = q2.asAction
	->
	where q1 = q2

	//describes monic (ObsVar >--observesVar--> EnvVar)
	forall o2 o3 : ObsVar
	where o2.observesVar = o3.observesVar
	->
	where o2 = o3

	//describes epi (Obsv --observes-->> ObsVar)
	forall o1 : ObsVar
	->
	exists ob1 : Obsv
	where ob1.observes = o1
}


// Actuator schema
schema ActuatorSchema = literal : Type {
	imports 
		CompSchema
		EnvVarSchema
	entities
		Actuator
		ActState
		ActTrans
		Infl
	foreign_keys
		asCompA		: Actuator -> Comp
		//compM 	: Mode -> Comp
		//pre		: Transition -> Mode
		//post		: Transition -> Mode
		mode 		: ActState -> Mode
		trans		: ActTrans -> Transition
		preA		: ActTrans -> ActState
		postA		: ActTrans -> ActState
		actS		: ActState -> Actuator
		actI		: Infl -> Actuator
		varI		: Infl -> EnvVar
	attributes
		ActuatorName : Actuator -> String
		ActuatorType : Actuator -> String
		
		//sensorOpRange : Sensor -> Float
		//sensorNoise : Sensor -> Float
		//sensorResolution : Sensor -> Float
		//sensorAccuracy : Sensor -> Float
		//sensorOutputRate : Sensor -> Float
		//sensorPowerConsume : Sensor -> Float
	path_equations
		ActTrans.postA.mode = ActTrans.trans.post
		ActTrans.preA.mode = ActTrans.trans.pre
		ActState.mode.compM = ActState.actS.asComp
		
	observation_equations
		
}


// Mapping from EnvVar schema to Actuator schema
mapping EnvVar2Actuator = literal : EnvVarSchema -> ActuatorSchema {
	imports identity EnvVarSchema
}


// Mapping from Comp schema to Actuator schema
mapping Comp2Actuator = literal : CompSchema -> ActuatorSchema {
	imports identity CompSchema
}


// Constraints for ActuatorSchema
constraints ActuatorConst = literal : ActuatorSchema {
	//describes monic (Actuator >--asComp--> Comp)
	forall a1 a2 : Actuator
	where a1.asComp = a2.asComp
	->
	where a1 = a2
}

