ASD WaterTanks:
	enum OpenClosed : open closed
	utype FlowRate Real m3/s
	utype Area Real m3
	utype Height Real meters
	element Source physical 
		ports {
			out WO FlowRate {}
		}
	element Drain physical
		ports {
			in WI FlowRate
		}
	element Tank physical
		ports {
			in WI FlowRate
			in VI OpenClosed
			out WO FlowRate {WI, VI} 
			out WL Height {}
		}
	compound WaterTank continuous subsystem
		vars {
			h Height "0" Var
			a Area Parameter
			r FlowRate Parameter
		}
		ports {
			in VI OpenClosed
			out WLO Height {}
		}
	compound Controller discrete cyber
		ports {
			in WLI Height
			out VO OpenClosed "closed" {}
		}
	system WaterTankSys
	composition CWaterTank WaterTankSys->WaterTank : compulsory 1
	composition CController WaterTankSys->Controller : compulsory 1
	composition CSource WaterTank->Source : compulsory 1
	composition CTank WaterTank->Tank : compulsory 1
	composition CDrain WaterTank->Drain : compulsory 1
