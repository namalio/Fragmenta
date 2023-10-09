ASD ThreeWaterTanks:
	enum OpenClosed : open closed
	utype FlowRate Real m3/s
	utype Area Real m3
	utype Height Real meters
	system ThreeWaterTanks 
	compound TanksControl1 continuous subsystem
	compound TanksControl2 continuous subsystem
	compound Controller discrete cyber
		ports {out v1 OpenClosed "closed" {}}
	element Valve physical 
		vars {
			v OpenClosed Var
		}
		ports {
			in v2 OpenClosed 
			out w FlowRate {v2}
		}
	element WaterTank physical 
		vars {
			h Height "0" Var
			a Area Parameter
			r FlowRate Parameter
		}
		ports {
			in win FlowRate
			out wout FlowRate {win}
		}
	composition CTanksControl1 ThreeWaterTanks->TanksControl1 : compulsory 1
	composition CTanksControl2 ThreeWaterTanks->TanksControl2 : compulsory 1
	composition CController ThreeWaterTanks->Controller : compulsory 1
	composition CValve TanksControl1->Valve : compulsory 1
	composition CWaterTank1 TanksControl1->WaterTank : compulsory 1
	composition CWaterTank2 TanksControl2->WaterTank : compulsory 2
