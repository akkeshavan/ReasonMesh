(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-fun circuit () Bool)
(declare-fun grn () Bool)
(declare-fun grn_MR () Bool)
(declare-fun grn_SR () Bool)
(declare-fun org () Bool)
(declare-fun org_MR () Bool)
(declare-fun org_SR () Bool)
(declare-fun prt () Bool)
(declare-fun rd1 () Bool)
(declare-fun rd2 () Bool)
(declare-fun red_MR () Bool)
(declare-fun red_SR () Bool)

(assert (! (=> 
               grn 
               (and 
                   (not 
                       org) 
                   (not 
                       rd1) 
                   (not 
                       rd2)))
         :named hyp1))
(assert (! (=> 
               org 
               (and 
                   (not 
                       rd1) 
                   (not 
                       rd2)))
         :named hyp2))
(assert (! (=> 
               rd1 
               (not 
                   rd2))
         :named hyp3))
(assert (! (= 
               grn_MR 
               grn)
         :named hyp4))
(assert (! (= 
               org_MR 
               org)
         :named hyp5))
(assert (! (= 
               grn_SR 
               rd1)
         :named hyp6))
(assert (! (= 
               org_SR 
               rd2)
         :named hyp7))
(assert (! (= 
               red_SR 
               (or 
                   grn 
                   org))
         :named hyp8))
(assert (! (= 
               red_SR 
               (or 
                   grn_MR 
                   org_MR))
         :named hyp9))
(assert (! circuit
         :named hyp10))
(assert (! rd2
         :named hyp11))
(assert (! red_MR
         :named hyp12))
(assert (! (or 
               grn_SR 
               org_SR)
         :named hyp13))
(assert (! (not 
               (= 
                   org 
                   (and 
                       prt 
                       grn)))
         :named goal))
(check-sat)
(exit)

