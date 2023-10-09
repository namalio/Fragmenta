ASD Example:
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
