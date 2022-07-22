ASD Cash_Machine:
	enum OkFail : ok fail
	strt CardNo {}
	strt Date {
		day Interval 1 31
		month Interval 1 12
		year Int
	}
	strt Name {}
	strt PIN {}
	strt Bank {}
	strt TelephoneNo {}
	strt BillRefNo {}
	strt CardInfo {
		cNo CardNo
		validDt Date
		holder Name
		bank Bank
		pin PIN
	}
	strt BillInfo {
		ref BillRefNo
		am Int
	}
	enum Options : withdraw balance payBill topUp returnCard
	strt MobilePhoneOperator {}
	strt TopUpInfo {
		op MobilePhoneOperator
		pNo TelephoneNo
		am Int
	}
	enum CardReaderMsgs : cardIn cardCollected collectTimeout
	interface BankCmds {
	   operation withdraw OkFail {
	      cNo CardNo
	      am Int
	   }
	}
	system CashMachineSys