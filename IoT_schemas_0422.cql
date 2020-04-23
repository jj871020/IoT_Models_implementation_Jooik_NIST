// implementation for "Compositional Models for the Internet of Things" paper

typeside Type = literal { 
	java_types
		Fn = "jdk.nashorn.api.scripting.JSObject"
		BinFn = "jdk.nashorn.api.scripting.JSObject"
		String = "java.lang.String"
		Float = "java.lang.Double"
		Int = "java.lang.Integer"
		// HVAC computation
		//ObsVar = "jdk.nashorn.api.scripting.JSObject"

	java_constants
		Fn = "throw new RuntimeException()"
		BinFn = "throw new RuntimeException()"
		String = "return input[0]"
		Float = "return 0.0 + java.lang.Double.parseDouble(input[0])"
		Int = "return 0 + java.lang.Integer.parseInt(input[0])"
		//HVAC computation
		//ObsVar = "throw new RuntimeException()"
		

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
		//HVAC computation
		//ObsVar1 : Float -> ObsVar = "return new javax.script.ScriptEngineManager().getEngineByName(\"nashorn\").eval(input[0])"
		//ObsVar2 : Float, ObsVar -> ObsVar = "return \"\"+input[0].call(input[0],input[1])"
		//control : 
		
}




// Portgraph
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
		sensorName : Sensor -> String
		sensorOpRange : Sensor -> Float
		sensorNoise : Sensor -> Float
		sensorResolution : Sensor -> Float
		sensorAccuracy : Sensor -> Float
		sensorOutputRate : Sensor -> Float
		sensorPowerConsume : Sensor -> Float
		//message
		cmndStr : SensorCmnd -> String
		cmndFormat : Sensor -> Fn
		
}


// Mapping from EnvVar schema to Sensor schema
mapping EnvVar2Sensor = literal : EnvVarSchema -> SensorSchema {
	imports identity EnvVarSchema
}
 

// Mapping from Comp schema to Sensor schema
mapping Comp2Sensor = literal : CompSchema -> SensorSchema {
	imports identity CompSchema
} 



/*
mapping SensorIsComp = literal : SensorSchema -> CompSchema {
	
	//entity
		//SensorCmnd -> Cmnd
	//foreign_keys
		//sensorC -> compC
	
	entity
		Sensor -> Comp
	attributes
		sensorName -> compName
		cmndFormat -> cmndFormat
	
}
// need mapping from sensor to component just like therm to sensor?
*/



// Constraints for SensorSchema
constraints SensorConst = literal : SensorSchema {
	imports CompConst

/*
	// sensor name is a key for sensors
	forall r1 r2 : Sensor
	where r1.sensorName = r2.sensorName
	->
	where r1 = r2
*/


/*
	// if SensorCmnd >--cmndS--> Cmnd
	forall c1 c2 : SensorCmnd
	where c1.cmndS = c2.cmndS
	->
	where c1 = c2
*/


	
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





// instantiation of thermometer catalogs
instance testSensorData = literal : SensorSchema {
	generators 
		th1 th2 th3 : Sensor
		cmnd1a cmnd1b cmnd2a cmnd2b cmnd3 : SensorCmnd
		adr1 adr2a adr2b adr3a adr3b : Addr
		channel1 channel2 : Channel
		action1 action2: Action
	equations
		sensorC(cmnd1a)=th1	sensorC(cmnd1b)=th1
		sensorC(cmnd2a)=th2	sensorC(cmnd2b)=th2
		sensorC(cmnd3)=th3

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




		// cmnd2a = ON, channel(cmnd2a) = channel1
		// channel1(caller) = addr1, channel1(invoke) = addr2a
		// addr1 = TMP36, IP, 192.168.0.1
		// addr2a = DS18B20, IP, 123.45.67.89
		
		// cmnd3 = Power, channel(cmnd3) = channel2
		// channel2(caller) = addr2b, channel2(invoke) = addr3b
		// addr2b = DS18B20, Bluetooth, 11:22:33:44:EE:FF
		// addr3b = BME280, Bluetooth, 00:11:22:33:FF:EE
		
		
		action1.channel = channel1
		action1.invokes = cmnd2a.cmndS
	
		action2.channel = channel2
		action2.invokes = cmnd3.cmndS

		channel1.addr1 = adr1
		channel1.addr2 = adr2a
		
		channel2.addr1 = adr2b
		channel2.addr2 = adr3b

		adr1.ofComp.compName = "TMP36" 
		adr1.address="192.168.0.1"
		adr1.protocol.protocolName="IP"

		adr2a.ofComp.compName = "DS18B20" 
		adr2a.address="123.45.67.89"
		adr2a.protocol.protocolName="IP"
		
		adr2b.ofComp.compName = "DS18B20" 
		adr2b.address="11:22:33:44:EE:FF"
		adr2b.protocol.protocolName="Bluetooth"
		
		adr3a.ofComp.compName = "BME280" 
		adr3a.address="145.36.43.1"
		adr3a.protocol.protocolName="IP"

		adr3b.ofComp.compName = "BME280" 
		adr3b.address="00:11:22:33:FF:EE"
		adr3b.protocol.protocolName="Blutooth"

		// Rather than introduce a protocol generator, we
		// can reference the protocol through an address.
		adr1.protocol.msgFormat = parse2("function (s1,s2) {return \"msg:{addr:\" + s1 + \",cmnd:\" + s2 + \"}\"}")
		adr2b.protocol.msgFormat = parse2("function (s1,s2) {return \"Message(\" + s2 + \",\" + s1 + \")\"}")


	options
		require_consistency = false
		allow_java_eqs_unsafe = true
}


// test
instance testSensor = chase SensorConst testSensorData {
	options
		require_consistency = false
		allow_java_eqs_unsafe = true
	
}








// Actuator schema
schema ActuatorSchema = literal : Type {
	imports 
		ACSchema
		FanSchema
		CompSchema
		EnvVarSchema
	entities
		Actuator
		ActState
		ActTrans
		Infl
	foreign_keys
		acisActuator : AC -> Actuator
		fanisActuator : Fan -> Actuator
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
		powerConsume : Actuator -> Float
	observation_equations
		forall x. x.acisActuator.actuatorType = "AC"
		forall y. y.acisActuator.actuatorName = y.ACName
		forall z. z.acisActuator.powerConsume = z.ACpowerConsume
		forall a. a.fanisActuator.actuatorType = "Fan"
		forall b. b.fanisActuator.actuatorName = b.FanName
		forall c. c.fanisActuator.powerConsume = c.FanpowerConsume
	options
		allow_java_eqs_unsafe=true 
		
}


// AC schema
schema ACSchema = literal : Type {
	entities
		AC
	attributes

		ACName : AC-> String
		ACpowerConsume : AC-> Float
		//specific to AC
		airflow : AC-> Float
		coolingCapacity : AC-> Float
		energyEffRatio : AC-> Float
			
}





// Mapping from EnvVar schema to Actuator schema
mapping EnvVar2Actuator = literal : EnvVarSchema -> ActuatorSchema {
	imports identity EnvVarSchema
}


// Mapping from Comp schema to Actuator schema
mapping Comp2Actuator = literal : CompSchema -> ActuatorSchema {
	imports identity CompSchema
}


// Mapping from AC schema to Actuator schema
mapping AC2Actuator = literal : ACSchema -> ActuatorSchema {
	imports identity ACSchema
}


// Constraints for ActuatorSchema
constraints ActuatorConst = literal : ActuatorSchema {
	//describes monic (Actuator >--asComp--> Comp)
	forall a1 a2 : Actuator
	where a1.asCompA = a2.asCompA
	->
	where a1 = a2
}





 
// instantiation of AC catalogs
instance testACData = literal : ACSchema {
	generators 
		ac1 ac2 ac3 : AC
	equations 


		ACName(ac1) = "test AC 1"
		ACName(ac2) = "test AC 2"
		ACName(ac3) = "test AC 3"

		ACpowerConsume(ac1) = "1"
		ACpowerConsume(ac2) = "2"
		ACpowerConsume(ac3) = "3"

		airflow(ac1) = "1"
		airflow(ac2) = "2"
		airflow(ac3) = "3"

		coolingCapacity(ac1) = "1"
		coolingCapacity(ac2) = "2"
		coolingCapacity(ac3) = "3"

		energyEffRatio(ac1) = "1"
		energyEffRatio(ac2) = "2"
		energyEffRatio(ac3) = "3"
		
}


instance pushAC = sigma AC2Actuator testACData




// Fan schema
schema FanSchema = literal : Type {
	entities
		Fan
	attributes
		
		FanName : Fan-> String
		FanpowerConsume : Fan-> Float
		//specific to Fan
		airflow : Fan-> Float
		CFM : Fan-> Float
		energyEffRatio : Fan-> Float
		

}


// Mapping from AC schema to Actuator schema
mapping Fan2Actuator = literal : FanSchema -> ActuatorSchema {
	imports identity FanSchema
}




// instantiation of Fan catalogs
instance testFanData = literal : FanSchema {
	generators 
		fan1 fan2 fan3 : Fan
	equations 
	

		FanName(fan1) = "test Fan 1"
		FanName(fan2) = "test Fan 2"
		FanName(fan3) = "test Fan 3"

		FanpowerConsume(fan1) = "1"
		FanpowerConsume(fan2) = "2"
		FanpowerConsume(fan3) = "3"

		airflow(fan1) = "1"
		airflow(fan2) = "2"
		airflow(fan3) = "3"

		CFM(fan1) = "1"
		CFM(fan2) = "2"
		CFM(fan3) = "3"

		energyEffRatio(fan1) = "1"
		energyEffRatio(fan2) = "2"
		energyEffRatio(fan3) = "3"

}


instance pushFan = sigma Fan2Actuator testFanData



// build catalog as colimit

