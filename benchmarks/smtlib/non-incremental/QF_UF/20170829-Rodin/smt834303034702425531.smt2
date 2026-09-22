(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-fun circuit () Bool)
(declare-fun grn () Bool)
(declare-fun org () Bool)
(declare-fun prt () Bool)
(declare-fun rd1 () Bool)
(declare-fun rd2 () Bool)

(assert (! circuit
         :named hyp1))
(assert (! (not 
               (or 
                   (and 
                       prt 
                       grn) 
                   org 
                   (and 
                       (not 
                           prt) 
                       rd1) 
                   rd2 
                   (and 
                       grn 
                       (not 
                           prt)) 
                   (and 
                       rd1 
                       prt)))
         :named goal))
(check-sat)
(exit)

