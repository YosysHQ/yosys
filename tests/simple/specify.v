module test_specify;

specparam a=1;

specify
endspecify

specify
(A => B) = ( 1 ) ;
(A- => B) = ( 1,2 ) ;
(A+ => B) = ( 1,2,3 ) ;
(A => B) = (
 1.1, 2, 3,
 4, 5.5, 6.6
) ;
(A => B) = (
 1.1, 2, 3,
 4, 5.5, 6.6 ,
 7.7, 8.8, 9,
 10.1, 11, 12
) ;
specparam b=1;
specparam [1:2] asasa=1;
endspecify

specify
specparam c=1:2:3;
endspecify

endmodule

