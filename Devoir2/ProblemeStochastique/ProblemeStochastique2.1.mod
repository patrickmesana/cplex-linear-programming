/*********************************************
 * OPL 12.6.3.0 Model
 * Author: patrickmesana
 * Creation Date: 2016-03-26 at 7:32:54 PM
 *********************************************/

 int vendredi = ...;
 int nrbAP = ...;
 int nbrAS = ...;
 range jours = 1..vendredi;
 range aps = 1..nrbAP;
 range ass = 1..nbrAS;
 int analyses[jours] = ...;
 int CAP = ...; // Cout par jour d'un Analyste Permanent (AP)
 int CAS = ...; // Cout par jour d'un Analyste Surnumenaire (AS)
 int CHSP = ...; // Cout Heure Sup d'un AP
 int CHSS = ...; // Cout Heure Sup d'un AS
 int RAP = ...; // Rendement d'un AP
 int RAS = ...; // Rendement d'un AS
 int coutDeDepassement = ...;

// ***********************
// Variables de decision
// ***********************
dvar boolean AP[aps][jours];
dvar boolean AS[ass][jours]; 
dvar int+ HSp; //heures sup d'un AP
dvar int+ HSs; //heures sup d'un AS
dvar int+ S[jours];//stock au debut de la journee
 
// ***********************
// Fonction-objectif
// ***********************
minimize sum (a in aps, j in jours) AP[a][j] * CAP +
		sum (a in ass, j in jours) AS[a][j] * CAS +
		HSp * CHSP +
		HSs * CHSS + 
		sum (j in jours) S[j] * coutDeDepassement;
 
// ***********************
// Expressions
// ***********************
//heures d'analyse par AP dans la journee
dexpr int HAP[j in jours] = 7 * sum(i in aps) AP[i][j];
//heures d'analyse par AS dans la journee
dexpr int HAS[j in jours] = 7 * sum(i in ass) AS[i][j];
//quantite d'analyses traitees dans la journee
dexpr int Q[j in jours] = HAP[j] * RAP + HAS[j] * RAS;
//quantites sup a traite
dexpr int Qs = HSp + HSs;


// ***********************
// Contraintes
// ***********************
subject to {

//On commence la semaine sans stock
S[1] == 0;

//les stocks est ce qui reste a faire a la fin de la journee
forall (j in 1..vendredi-1) S[j+1] == (analyses[j] + S[j]) - Q[j];
	
//Semaine de 4 jours pour AP
forall (a in aps) sum(j in jours) AP[a][j] == 4;

//5 AP max en conges par jour
forall (j in jours) sum(a in aps) AP[a][j] >= nrbAP - 5;

//heures suplementaires
analyses[vendredi] + S[vendredi] == Q[vendredi] + Qs;
HSp <= sum(a in aps) AP[a][vendredi] * 2;
HSs <= sum(a in ass) AS[a][vendredi] * 2;

}