This is an attempt to extend Oleg's ["Typed compilation via GADTs"](http://okmij.org/ftp/tagless-final/index.html#tc-GADT) code example. The intention is to add lets and lambdas, and support for polymorphism.

I've been trying to do this in my [FDL language](https://github.com/petermarks/FDL/tree/external-dsl), where I have taken a very similar approach to Oleg. I thought it might be easier to start from his clean base in isolation from the rest of my code.
