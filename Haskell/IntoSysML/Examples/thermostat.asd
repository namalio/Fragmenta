ASD Thermostat:
	enum OnOff : on off
	utype Temp Real C
	enum HeatingSt : heating idle
	strt Time {
		hour Interval 0 23
		minute Interval 0 59
	}
	strt Date {
		day Interval 1 31
		month Interval 1 12
		year Int
	}
	system Thermostat
	   ports {
	       in d1 Date
	       in ti1 Time
	       in si OnOff
	       in t1 Temp
	   }
	compound Heating continuous subsystem
	   vars {
			ct Temp Var
			dt Temp "20.0" Var
			s OnOff Var
			hst HeatingSt Var
		}
	   ports {
          in t4 Temp
          in s4 OnOff
	   }
	compound Controls continuous subsystem
	   vars {
			cd Date Var
			ct Time Var
		}
	   ports {
          in d2 Date
          in ti1 Time
          in t2 Temp
          in s2 OnOff
          out t3 Temp {t2}
          out s3 OnOff {s2}
	   }
	composition Thermostat Heating compulsory 1
	composition Thermostat Controls compulsory 1