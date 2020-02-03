// implementation for SIGMETRICS 2020 paper

typeside Type = literal { 
	java_types
		Fn = "jdk.nashorn.api.scripting.JSObject"
		BinFn = "jdk.nashorn.api.scripting.JSObject"
		String = "java.lang.String"
		Float = "java.lang.Double"
		Int = "java.lang.Integer"

	java_constants
		Fn = "throw new RuntimeException()"
		BinFn = "throw new RuntimeException()"
		String = "return input[0]"
		Float = "return 0.0 + java.lang.Double.parseDouble(input[0])"
		Int = "return 0 + java.lang.Integer.parseInt(input[0])"

	java_functions
		plus : Float,Float -> Float = "return (input[0] + input[1])"
		cat : String,String -> String = "return (input[0] + input[1])"
		cat3 : String,String,String -> String = "return (input[0] + input[1] + input[2])"
		// unary function
		parse : String -> Fn = "return new javax.script.ScriptEngineManager().getEngineByName(\"nashorn\").eval(input[0])"
		//binary function
		parse2 : String -> BinFn = "return new javax.script.ScriptEngineManager().getEngineByName(\"nashorn\").eval(input[0])"
		apply : Fn, String -> String = "return \"\"+input[0].call(input[0],input[1])"
		apply2 : BinFn, String, String -> String = "return \"\"+input[0].call(input[0],input[1],input[2])"
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
		caller		: Action -> Comp
		channel		: Action -> Channel
	path_equations
		Transition.pre.compM = Transition.post.compM
		Channel.addr1.protocol = Channel.addr2.protocol
		Action.channel.addr1.ofComp = Action.caller
		Action.channel.addr2.ofComp = Action.invokes.compC
	attributes
		compName 		: Comp -> String
		protocolName 	: Protocol -> String
		address			: Addr -> String
		cmndFormat  	: Comp -> Fn
		msgFormat 		: Protocol -> BinFn
		cmndStr 		: Cmnd -> String
		// Defined attributes
		cmnd 			: Cmnd -> String
		msg				: Action -> String
	observation_equations
		forall c. cmnd(c)=apply(cmndFormat(c.compC),c.cmndStr)
		forall a. msg(a)=apply2(msgFormat(a.channel.addr1.protocol),address(a.channel.addr2),cmnd(a.invokes))
}


// Constraints for CompSchema
constraints CompConst = literal : CompSchema {
	
	// component name is a key for components
	forall c1 c2 : Comp
	where c1.compName = c2.compName
	->
	where c1 = c2

	// protocol name is a key for protocols
	forall p1 p2 : Protocol
	where p1.protocolName = p2.protocolName
	->
	where p1 = p2

	// address is a key for channels
	forall ch1 ch2 : Channel
	where ch1.addr1 = ch2.addr1		ch1.addr2=ch2.addr2
	->
	where ch1 = ch2
	


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
		SensorCmnd
	foreign_keys
		asCompS 	: Sensor -> Comp
		sensorC		: SensorCmnd -> Sensor			// pullback constraint 
		cmndS		: SensorCmnd -> Cmnd
		asCmnd		: Obsv -> SensorCmnd
		asAction 	: Query -> Action
		invokesQ	: Query -> Obsv
		value 		: Query -> EnvState
		varE		: EnvState -> EnvVar
		varO		: Obsv -> EnvVar
		observes 	: Obsv -> ObsVar
		observesVar	: ObsVar -> EnvVar
	path_equations
		Query.value.varE = Query.invokesQ.varO
		SensorCmnd.sensorC.asCompS = SensorCmnd.cmndS.compC
	attributes
		sensorType : Sensor -> String
		sensorOpRange : Sensor -> Float
		sensorNoise : Sensor -> Float
		sensorResolution : Sensor -> Float
		sensorAccuracy : Sensor -> Float
		sensorOutputRate : Sensor -> Float
		sensorPowerConsume : Sensor -> Float
}


// Mapping from EnvVar schema to Sensor schema
mapping EnvVar2Sensor = literal : EnvVarSchema -> SensorSchema {
	imports identity EnvVarSchema
}


// Mapping from Comp schema to Sensor schema
mapping Comp2Sensor = literal : CompSchema -> SensorSchema {
	imports identity CompSchema
}

// Thermometer schema
schema ThermSchema = literal : Type {
	entities
		Therm Cmnd
	foreign_keys
		compC : Cmnd -> Therm
	attributes
		sensorType : Therm-> String
		sensorName : Therm-> String
		sensorOpRange : Therm-> Float
		sensorNoise : Therm-> Float
		sensorResolution : Therm-> Float
		sensorAccuracy : Therm -> Float
		sensorOutputRate : Therm-> Float
		sensorPowerConsume : Therm -> Float
		cmndStr : Cmnd -> String
		cmndFormat : Therm -> Fn
}

// mapping from Sensor schema to Thermometer schema
mapping thermIsSensor = literal : ThermSchema -> SensorSchema {
	entity
		Therm -> Sensor
	attributes	
		// Attributes of Components
		sensorName -> asCompS.compName 
		cmndFormat -> asCompS.cmndFormat
		// Attributes of Sensor
		sensorType -> sensorType 
		sensorOpRange -> sensorOpRange 
		sensorNoise -> sensorNoise 
		sensorResolution -> sensorResolution 
		sensorAccuracy -> sensorAccuracy 
		sensorOutputRate -> sensorOutputRate
		sensorPowerConsume -> sensorPowerConsume
	entity
		Cmnd -> SensorCmnd
	foreign_keys
		compC -> sensorC
	attributes
		cmndStr -> cmndS.cmndStr
}

// instantiation of thermometer catalogs
instance testThermData = literal : ThermSchema {
	generators 
		th1 th2 th3 : Therm
		cmnd1a cmnd1b cmnd2a cmnd2b cmnd3 : Cmnd
	equations
		compC(cmnd1a)=th1	compC(cmnd1b)=th1
		compC(cmnd2a)=th2	compC(cmnd2b)=th2
		compC(cmnd3)=th3

		cmndStr(cmnd1a)="TurnOn"		cmndStr(cmnd1b)="TurnOff"
		cmndStr(cmnd2a)="ON"			cmndStr(cmnd2b)="OFF"
		cmndStr(cmnd3)="Power"

		sensorType(th1) = "Thermometer"
		sensorType(th2) = "Thermometer"
		sensorType(th3) = "Thermometer"

		sensorName(th1) = "TMP36"
		sensorName(th2) = "DS18B20"
		sensorName(th3) = "BME280"

		sensorOpRange(th1) = "1"
		sensorOpRange(th2) = "2"
		sensorOpRange(th3) = "3"

		sensorNoise(th1) = "1"
		sensorNoise(th2) = "2"
		sensorNoise(th3) = "3"

		sensorResolution(th1) = "1"
		sensorResolution(th2) = "2"
		sensorResolution(th3) = "3"

		sensorAccuracy(th1) = "1"
		sensorAccuracy(th2) = "2"
		sensorAccuracy(th3) = "3"

		sensorOutputRate(th1) = "1"
		sensorOutputRate(th2) = "2"
		sensorOutputRate(th3) = "3"

		sensorPowerConsume(th1) = "1"
		sensorPowerConsume(th2) = "2"
		sensorPowerConsume(th3) = "3"

		cmndFormat(th1) = parse("function (s) {return s+\"()\"}")
		cmndFormat(th2) = parse("function (s) {return \"{action:\" + s + \"}\"}")
		cmndFormat(th3) = parse("function (s) {return \"Action(\" + s + \")\"}")
}



// Constraints for SensorSchema
constraints SensorConst = literal : SensorSchema {
	imports CompConst
	
	//describes monic (Sensor >--asComp--> Comp)
	forall s1 s2 : Sensor 
	where s1.asCompS = s2.asCompS
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

instance pushTherm = sigma thermIsSensor testThermData


// instantiation via reference 
instance extendTherm = literal : SensorSchema {
	imports pushTherm
	generators
		addr1 addr2a addr2b addr3a addr3b : Addr
		channel1 channel2 : Channel
		action1 action2: Action
	equations

		action1.channel = channel1
		action1.invokes = cmnd2a.cmndS
	
		action2.channel = channel2
		action2.invokes = cmnd3.cmndS

		channel1.addr1 = addr1
		channel1.addr2 = addr2a
		
		channel2.addr1 = addr2b
		channel2.addr2 = addr3b

		addr1.ofComp.compName = "TMP36" 
		addr1.address="192.168.0.1"
		addr1.protocol.protocolName="IP"

		addr2a.ofComp.compName = "DS18B20" 
		addr2a.address="123.45.67.89"
		addr2a.protocol.protocolName="IP"
		
		addr2b.ofComp.compName = "DS18B20" 
		addr2b.address="11:22:33:44:EE:FF"
		addr2b.protocol.protocolName="Bluetooth"
		
		addr3a.ofComp.compName = "BME280" 
		addr3a.address="145.36.43.1"
		addr3a.protocol.protocolName="IP"

		addr3b.ofComp.compName = "BME280" 
		addr3b.address="00:11:22:33:FF:EE"
		addr3b.protocol.protocolName="Blutooth"

		// Rather than introduce a protocol generator, we
		// can reference the protocol through an address.
		addr1.protocol.msgFormat = parse2("function (s1,s2) {return \"msg:{addr:\" + s1 + \",cmnd:\" + s2 + \"}\"}")
		addr2b.protocol.msgFormat = parse2("function (s1,s2) {return \"Message(\" + s2 + \",\" + s1 + \")\"}")


	options
		require_consistency = false
		allow_java_eqs_unsafe = true
}

// test
instance testTherm = chase SensorConst extendTherm {
	options
		require_consistency = false
		allow_java_eqs_unsafe = true
	
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
		mode 		: ActState -> Mode
		trans		: ActTrans -> Transition
		preA		: ActTrans -> ActState
		postA		: ActTrans -> ActState
		actS		: ActState -> Actuator
		actI		: Infl -> Actuator
		varI		: Infl -> EnvVar
	path_equations
		ActTrans.postA.mode = ActTrans.trans.post
		ActTrans.preA.mode = ActTrans.trans.pre
		ActState.mode.compM = ActState.actS.asCompA
	attributes
		actuatorName : Actuator -> String
		actuatorType : Actuator -> String
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
	where a1.asCompA = a2.asCompA
	->
	where a1 = a2
}


// AC schema
schema ACSchema = literal : Type {
	entities
		AC
	attributes
		actuatorType : AC-> String
		actuatorName : AC-> String

}

// mapping from Actuator schema to AC schema
mapping ACIsActuator = literal : ACSchema -> ActuatorSchema {
	entity
		AC -> Actuator
	attributes	
		actuatorType -> actuatorType 
		actuatorName -> asCompA.compName 

}

// instantiation of AC catalogs
instance testACData = literal : ACSchema {
	generators 
		ac1 ac2 ac3 : AC
	equations 
		actuatorType(ac1) = "AC"
		actuatorType(ac2) = "AC"
		actuatorType(ac3) = "AC"

		actuatorName(ac1) = "test1"
		actuatorName(ac2) = "test2"
		actuatorName(ac3) = "test3"


	
}

