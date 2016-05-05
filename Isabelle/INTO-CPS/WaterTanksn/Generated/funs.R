
load_data<-function () {
  setwd("/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/Generated/")
  return(read.table("simulation.csv",header=T,sep=",",dec="."))
}

#create function for the fourth order polynomial
fourth_order <- function(newdist, model) {
    coefs <- coef(model)
    #y=ax^4 + bx^3 + cx^2 + dx + e
    res <- coefs[1] + (coefs[2] * newdist) + (coefs[3] * newdist^2) + (coefs[4] * newdist^3) + (coefs[5] * newdist^4)
    return(res)
}

#create function for the third order polynomial
third_order <- function(newdist, model) {
    coefs <- coef(model)
    #y=ax^3 + bx^2 + cx + e
    res <- coefs[1] + (coefs[2] * newdist) + (coefs[3] * newdist^2) + (coefs[4] * newdist^3)
    return(res)
}

#create function for the 2nd order polynomial
second_order <- function(newdist, model) {
    coefs <- coef(model)
    #y=ax^2 + bx + e
    res <- coefs[1] + (coefs[2] * newdist) + (coefs[3] * newdist^2)
    return(res)
}

draw_csp_curve<-function (dt) {
  dt_csp<-dt[dt$Environment=="CSP",]
  plot(dt_csp$Size, dt_csp$Time, col = "red", typ='l', frame.plot=FALSE,
    xlab="No of Nodes of the graph", axes=F, lwd=1, lty =2,
    ylab="Duration (s)", main="Algebraic loops: CSP")

  # draws the minor ticks of x axis
  par(tcl=-0.2)
  axis(side = 1, at = seq(from = 0, to = 400, by = 10), labels=F)
  # draws major ticks of x axis
  par(tcl= -0.5)
  axis(side = 1, at = seq(from = 0, to = 400, by = 50))
  # draws the minor ticks of y axis
  par(tcl=-0.2)
  axis(side = 2, at = seq(from = 0, to = 165, by = 1), labels=F)
  # draws major ticks of y axis
  par(tcl= -0.5)
  axis(side=2, at = seq(from = 0, to = 165, by = 5))

}

draw_plot_csp<-function () {
  setwd("/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/Generated/")
  dt<-read.table("simulation-csp.csv",header=T,sep=",",dec=".")

  draw_csp_curve(dt)
}


draw_plot_csp_with_estimate<-function () {
  setwd("/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/Generated/")
  dt<-read.table("simulation-csp.csv",header=T,sep=",",dec=".")

  draw_csp_curve(dt)

  xx <- seq(0, 407, length=400)
  fit3 <- lm(dt$Time~poly(dt$Size,3,raw=TRUE))

  yy<-third_order(xx, fit3)
  lines(xx, yy, col="blue", lwd=2)

  legend("top", col=c("blue", "red"), c("Estimate", "Data"), lty=c(1,2), lwd=c(2,1))
  #y=ax^3 + bx^2 + cx + d
  coefs <- coef(fit3)
  a <- round(coefs[4], 6)
  b <- round(coefs[3], 3)
  c <- round(coefs[2], 3)
  d <- round(coefs[1], 3)
  text(0,100,paste("y=",a,"*x^3+",b,"*x^2+",c,"*x+",d,sep=""), pos=4)
}

draw_johnson_curve<-function (dt) {
  plot(dt$Size, dt$Time, col = "red", typ='l', frame.plot=FALSE,
    xlab="No of Nodes of the graph", axes=F,
    ylab="Duration (s)", main="Algebraic loops: Johnson Algorithm")

  # draws the minor ticks of x axis
  par(tcl=-0.2)
  axis(side = 1, at = seq(from = 0, to = 400, by = 10), labels=F)
  # draws major ticks of x axis
  par(tcl= -0.5)
  axis(side = 1, at = seq(from = 0, to = 400, by = 50))
  # draws ticks of y axis
  par(tcl= -0.5)
  axis(side=2, at = seq(from = 0, to = 0.04, by = 0.01))

  legend("topright", col=c("blue", "red"), c("Estimate", "Data"), lty=c(1,1))

}

draw_csp_johnson<-function (dt) {
  setwd("/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/Generated/")
  dt_j<-read.table("simulation-johnson.csv",header=T,sep=",",dec=".")

  dt_csp<-read.table("simulation-csp.csv",header=T,sep=",",dec=".")

  plot(dt_csp$Size,dt_csp$Time, col = "blue", xlab="No of Nodes of the graph", ylab="Duration (s)",
    main="Algebraic loops: CSP vs Johnson Algorithm", lwd=2, lty =2,
    frame.plot=FALSE, typ='l', axes=F)

  points(dt_j$Size, dt_j$Time, col="red", typ='l')

  # draws the minor ticks of x axis
  par(tcl=-0.2)
  axis(side = 1, at = seq(from = 0, to = 400, by = 10), labels=F)
  # draws major ticks of x axis
  par(tcl= -0.5)
  axis(side = 1, at = seq(from = 0, to = 400, by = 50))
  # draws the minor ticks of y axis
  par(tcl=-0.2)
  axis(side = 2, at = seq(from = 0, to = 165, by = 1), labels=F)
  # draws the minor ticks of y axis
  par(tcl=-0.2)
  axis(side = 2, at = seq(from = 0, to = 165, by = 1), labels=F)
  # draws major ticks of y axis
  par(tcl= -0.5)
  axis(side=2, at = seq(from = 0, to = 165, by = 5))

  legend("top", col=c("blue", "red"), c("CSP", "Johnson"), lty=c(2,1), lwd =c(2,1))

  points(dt_csp[dt_csp$Time==max(dt_csp$Time),]$Size, max(dt_csp$Time), col="violet")
  maxTm<-round(max(dt_csp$Time), 2)
  text(dt_csp[dt_csp$Time==max(dt_csp$Time),]$Size, max(dt_csp$Time), labels=c(maxTm), cex= 1, pos=2)
  dt_j<-dt_j[dt_j$Size>=10,]
  maxTm<-round(max(dt_j$Time), 2)
  points(dt_j[dt_j$Time==max(dt_j$Time),]$Size, max(dt_j$Time), col="violet")
  text(dt_j[dt_j$Time==max(dt_j$Time),]$Size, max(dt_j$Time), labels=c(maxTm), cex= 1, pos=3)

}

draw_plot_johnson<-function () {
  setwd("/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/Generated/")
  dt<-read.table("simulation-johnson.csv",header=T,sep=",",dec=".")

  draw_johnson_curve(dt)

  fit  <- lm(dt$Time~dt$Size)
  xx <- seq(0, 407, length=400)
  lines(xx, predict(fit, data.frame(x=xx)), col="blue", lwd=2)

  #y=ax + b
  coefs <- coef(fit)
  a <- round(coefs[2], 5)
  b <- round(coefs[1], 5)
  text(6,0.01,paste("y=",a,"*x+",b,sep=""), pos=4)

  legend("topright", col=c("blue", "red"), c("Estimate", "Data"), lty=c(1,1), lwd=c(2, 1))
}

draw_alloy_curve<-function (data) {
  dt_alloy<-data[data$Environment=="Alloy",]
  plot(dt_alloy$Size,dt_alloy$Time, col = "blue", xlab="No of Nodes of the graph", ylab="Duration (s)",
    main="Algebraic loops: Alloy vs CSP",
    frame.plot=FALSE, lwd=1, lty=2,
    ylim=c(0, 700), xlim=c(0, 180), typ='l', axes=F)
  # x axis
  axis(side = 1, at = seq(from = 0, to = 180, by = 10))
  # y axis
  par(tcl=-0.2)
  #draws the minor ticks
  axis(side = 2, at = seq(from = 0, to = 700, by = 10), labels=F)
  #draws the major ticks
  par(tcl= -0.5)
  axis(side=2, at = seq(from = 0, to = 700, by = 50))
}

draw_plot_alloy<-function () {
  data<-load_data()
  draw_alloy_curve(data)
}

draw_plot_alloy_with_estimate<-function () {

  data<-load_data()
  dt_alloy<-data[data$Environment=="Alloy",]
  draw_alloy_curve(data)
  xx <- seq(0, 173, length=166)
  m.e <- nls(dt_alloy$Time ~ I(exp(1)^(a + b * dt_alloy$Size)), data = dt_alloy, start = list(a=0, b=0.1))
  lines(xx, predict(m.e, data.frame(x=xx)), col="red", lwd=2)
  a <- round(summary(m.e)$coefficients[1, 1], 4)
  b <- round(summary(m.e)$coefficients[2, 1], 4)
  text(0,150,paste("y=e^(",a,"+",b,"*x)",sep=""), pos=4)
  legend("top", col=c("blue", "red"), c("Data", "Estimate"), lty=c(2,1), lwd=c(1, 2))
}

draw_plot<-function () {
  data<-load_data()
  dt_alloy<-data[data$Environment=="Alloy",]
  data<-read.table("simulation-csp.csv",header=T,sep=",",dec=".")
  dt_csp<-data[data$Size<=173,]
  plot(dt_alloy$Size,dt_alloy$Time, col = "blue", xlab="No of Nodes of the graph", ylab="Duration (s)",
    main="Algebraic loops: Alloy vs CSP",
    frame.plot=FALSE,
    ylim=c(0, 700), xlim=c(0, 180), typ='l', axes=F)
  points(dt_csp$Size, dt_csp$Time, col="red", typ='l', lty = 2, lwd=2)
  # minor ticks of x axis
  par(tcl=-0.2)
  axis(side = 1, at = seq(from = 0, to = 180, by = 5), labels=F)
  # major ticks of x axis
  par(tcl= -0.5)
  axis(side = 1, at = seq(from = 0, to = 180, by = 20))
  # minor ticks of y axis
  par(tcl=-0.2)
  axis(side = 2, at = seq(from = 0, to = 700, by = 10), labels=F)
  #draws the label on the right to indicate the 10s mark
  axis(side = 4, at = c(10), las=2)
  #draws major ticks of y axis
  par(tcl= -0.5)
  axis(side=2, at = seq(from = 0, to = 700, by = 50))
  legend("top", lty=c(1,2), col=c("blue", "red"), c("Alloy", "CSP"), lwd=c(1, 2))
  abline(h=c(10), lty="dotted")
  points(dt_csp[dt_csp$Time==max(dt_csp$Time),]$Size, max(dt_csp$Time), col="violet")
  maxTm<-round(max(dt_csp$Time), 2)
  text(dt_csp[dt_csp$Time==max(dt_csp$Time),]$Size, max(dt_csp$Time), labels=c(maxTm), cex= 1, pos=3)
  maxTm<-round(max(dt_alloy$Time), 2)
  points(dt_csp[dt_alloy$Time==max(dt_alloy$Time),]$Size, max(dt_alloy$Time), col="violet")
  text(dt_alloy[dt_alloy$Time==max(dt_alloy$Time),]$Size, max(dt_alloy$Time), labels=c(maxTm), cex= 1, pos=3)
}

draw_plot2<-function () {
  data<-load_data()
  dt_csp<-data[data$Environment=="CSP",]
  dt_csp<-dt_csp[dt_csp$Size<=70,]
  dt_alloy<-data[data$Environment=="Alloy",]
  dt_alloy<-dt_alloy[dt_alloy$Size<=70,]
  plot(dt_alloy$Size,dt_alloy$Time, col = "blue", xlab="No of Nodes of the graph", ylab="Duration (s)",
    main="Algebraic loops: Alloy vs CSP",
    frame.plot=FALSE,
    ylim=c(0, 6), xlim=c(0, 70), typ='l', axes=F)
  points(dt_csp$Size, dt_csp$Time, col="red", typ='l', lty = 2, lwd=2)
  # x axis
  axis(side = 1, at = seq(from = 0, to = 80, by = 10))
  # y axis
  #par(tcl=-0.2)
  #draws the minor ticks
  #axis(side = 2, at = seq(from = 0, to = 100, by = 10), labels=F)
  #draws the label on the right to indicate the 10s mark
  #axis(side = 4, at = c(10), las=2)
  #draws the major ticks
  #par(tcl= -0.5)
  axis(side=2, at = seq(from = 0, to = 8, by = 0.5))
  legend("top", lty=c(1,2), col=c("blue", "red"), c("Alloy", "CSP"), lwd=c(1, 2))
  #abline(h=c(10), lty="dotted")
  #points(dt_csp[dt_csp$Time==max(dt_csp$Time),]$Size, max(dt_csp$Time), col="violet")
  #maxTm<-round(max(dt_csp$Time), 2)
  #text(dt_csp[dt_csp$Time==max(dt_csp$Time),]$Size, max(dt_csp$Time), labels=c(maxTm), cex= 0.7, pos=3)
}

run_anova<-function () {
  data<-load_data()
  summary(aov(Time~Environment,data=data))
}

run_kruskal.test<-function () {
  data<-load_data()
  kruskal.test(Time~Environment, data=data)
}

box_plot_alloy_csp<-function () {
  data<-load_data()
  dt_csp<-data[data$Environment=="CSP",]
  dt_alloy<-data[data$Environment=="Alloy",]

  boxplot(dt_alloy$Time, dt_csp$Time,
    names=c("Alloy", "CSP"),
    col=c("red4", "lightskyblue"), ylab="Duration (s)")

  # calculate the means
  means<-c(mean(dt_alloy$Time, na.rm=T), mean(dt_csp$Time,na.rm=T) )

  # draws the means
  points(means,col="black",pch=8)
}
