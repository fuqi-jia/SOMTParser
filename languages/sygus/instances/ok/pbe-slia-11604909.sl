(set-logic SLIA)

(synth-fun f ((_arg_0 String)) String
    ((Start String (ntString))
    (ntString String (_arg_0 "" " " "." (str.++ ntString ntString) (str.replace ntString ntString ntString) (str.at ntString ntInt) (int.to.str ntInt) (ite ntBool ntString ntString) (str.substr ntString ntInt ntInt)))
    (ntInt Int (1 0 -1 1 (+ ntInt ntInt) (- ntInt ntInt) (str.len ntString) (str.to.int ntString) (ite ntBool ntInt ntInt) (str.indexof ntString ntString ntInt)))
    (ntBool Bool (true false (= ntInt ntInt) (str.prefixof ntString ntString) (str.suffixof ntString ntString) (str.contains ntString ntString)))))

(constraint (= (f "AIX 5.1") "5.1"))
(constraint (= (f "VMware ESX Server 3.5.0 build-110268") "3.5"))
(constraint (= (f "Linux Linux 2.6 Linux") "2.6"))
(constraint (= (f "Red Hat Enterprise AS 4 <2.6-78.0.13.ELlargesmp>") "2.6"))
(constraint (= (f "Microsoft <R> Windows <R> 2000 Advanced Server 1.0") "1.0"))
(constraint (= (f "Microsoft Windows XP Win2008R2 6.1.7601") "6.1"))

(check-synth)

