/*********************************************
 * OPL 12.6.3.0 Model
 * Author: patrickmesana
 * Creation Date: 2016-03-26 at 7:32:54 PM
 *********************************************/

 int vendredi = ...;
 int nrbAP = ...;
 int nbrAS = ...;
 range jours = 1..vendredi;
 range apGroups = 1..5;
 int analyses[jours] = ...;
 int CAP = ...; // Cout par jour d'un Analyste Permanent (AP)
 int CAS = ...; // Cout par jour d'un Analyste Surnumenaire (AS)
 int CHSP = ...; // Cout Heure Sup d'un AP
 int CHSS = ...; // Cout Heure Sup d'un AS
 int RAP = ...; // Rendement d'un AP
 int RAS = ...; // Rendement d'un AS
 int coutDeDepassement = ...;
 int combinaisonJoursAP[apGroups][jours] = ...;
 
// ***********************
// Variables de decision
// *********************** 
dvar int+ HSp; //heures sup d'un AP
dvar int+ HSs; //heures sup d'un AS
dvar int+ S[jours];//stock au debut de la journee
dvar int+ nbrAnP[jours];
dvar int+ nbrAnS[jours];
dvar int+ d[apGroups];

// ***********************
// Fonction-objectif
// ***********************
minimize sum(j in jours) nbrAnP[j] * CAP +
		sum (j in jours) nbrAnS[j] * CAS +
		HSp * CHSP +
		HSs * CHSS + 
		sum (j in jours) S[j] * coutDeDepassement;
 
// ***********************
// Expressions
// ***********************
//heures d'analyse par AP dans la journee
dexpr int HAP[j in jours] = 7 * nbrAnP[j];
//heures d'analyse par AS dans la journee
dexpr int HAS[j in jours] = 7 * nbrAnS[j];
//quantite d'analyses traitees dans la journee
dexpr int Q[j in jours] = HAP[j] * RAP + HAS[j] * RAS;
//quantites sup a traite
dexpr int Qs = HSp * RAP + HSs * RAS;

// ***********************
// Contraintes
// ***********************
subject to {

//On commence la semaine sans stock
S[1] == 0;

//les stocks est ce qui reste a faire a la fin de la journee
forall (j in 1..vendredi-1) S[j+1] == (analyses[j] + S[j]) - Q[j];
	
//Semaine de 4 jours pour AP
forall(j in jours) sum(g in apGroups) combinaisonJoursAP[j][g] * d[g] == nbrAnP[j];

//5 AP max en conges par jour et max des deux types
forall (j in jours){ 
	nbrAnP[j] >= nrbAP - 5;
	nbrAnP[j] <= nrbAP;
	nbrAnS[j] <= nbrAS;
}

//heures suplementaires
analyses[vendredi] + S[vendredi] == Q[vendredi] + Qs;
HSp <= nbrAnP[vendredi] * 2;
HSs <= nbrAnS[vendredi] * 2;

}