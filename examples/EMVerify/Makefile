.PHONY: contactless
contactless:
	#mastercard:
	# SDA
	m4 -DflMastercard -DflSDA -DflNoPIN -DflLow Contactless.tg.m4 > contactless/Mastercard_SDA_NoPIN_Low.tg
	m4 -DflMastercard -DflSDA -DflNoPIN -DflHigh Contactless.tg.m4 > contactless/Mastercard_SDA_NoPIN_High.tg
	m4 -DflMastercard -DflSDA -DflOnlinePIN -DflLow Contactless.tg.m4 > contactless/Mastercard_SDA_OnlinePIN_Low.tg
	m4 -DflMastercard -DflSDA -DflOnlinePIN -DHigh Contactless.tg.m4 > contactless/Mastercard_SDA_OnlinePIN_High.tg
	# DDA
	m4 -DflMastercard -DflDDA -DflNoPIN -DflLow Contactless.tg.m4 > contactless/Mastercard_DDA_NoPIN_Low.tg
	m4 -DflMastercard -DflDDA -DflNoPIN -DflHigh Contactless.tg.m4 > contactless/Mastercard_DDA_NoPIN_High.tg
	m4 -DflMastercard -DflDDA -DflOnlinePIN -DflLow Contactless.tg.m4 > contactless/Mastercard_DDA_OnlinePIN_Low.tg
	m4 -DflMastercard -DflDDA -DflOnlinePIN -DflHigh Contactless.tg.m4 > contactless/Mastercard_DDA_OnlinePIN_High.tg
	# CDA
	m4 -DflMastercard -DflCDA -DflNoPIN -DflLow Contactless.tg.m4 > contactless/Mastercard_CDA_NoPIN_Low.tg
	m4 -DflMastercard -DflCDA -DflNoPIN -DflHigh Contactless.tg.m4 > contactless/Mastercard_CDA_NoPIN_High.tg
	m4 -DflMastercard -DflCDA -DflOnlinePIN -DflLow Contactless.tg.m4 > contactless/Mastercard_CDA_OnlinePIN_Low.tg
	m4 -DflMastercard -DflCDA -DflOnlinePIN -DflHigh Contactless.tg.m4 > contactless/Mastercard_CDA_OnlinePIN_High.tg
	#visa:
	#EMV mode
	m4 -DflVisa -DflEMV -DflLow Contactless.tg.m4 > contactless/Visa_EMV_Low.tg
	m4 -DflVisa -DflEMV -DflHigh Contactless.tg.m4 > contactless/Visa_EMV_High.tg
	#DDA mode
	m4 -DflVisa -DflDDA -DflLow Contactless.tg.m4 > contactless/Visa_DDA_Low.tg
	m4 -DflVisa -DflDDA -DflHigh Contactless.tg.m4 > contactless/Visa_DDA_High.tg
	#visa-fix:
	m4 -DflVisa -DflDDA -DflLow -DflFix Contactless.tg.m4 > contactless/Visa_DDA_Low_Fix.tg
