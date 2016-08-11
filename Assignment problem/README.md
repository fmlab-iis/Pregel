# Assignment Problem Using Auction Algorithm

Given a bipartite graph. Two sets, one contains people and another contains objects.
Find an one-to-one relationship to make the benefit MAX.

***

## Algorithm Pseudo Code

Bidding Phase
set of unassigned person = I, i belong to I, i determines an object ji (BEST VALUE)
Submit a bid : pj+yi  ( yi=vi - wi + e, vi : best object ; wi : second best object ; e < 1/n )
Every unassigned person send bid to its best object.

Assignment Phase
Every object find the largest bid and assigned itself to that person and increase its price to highest bid. The person who was originally assigned to this object would leave without an object.

Terminate:
a.the auction terminates in a finite number of iterations, with all persons almost happy, before every object receives a bid
b.the auction continues until, after a finite number of rounds, all objects receive at least one bid, at which time the auction terminates.

***

## Pregel Implementation


PerssonVD: assignObj(VertexId), bid(Double), status(int)
ObjectVD  : owner(VertexID), price(Double)

initialMsg : A(-1L ,0 ,0 )

iteration : C/e e=constant
vprog : (VertexId, VD, A) ⇒ VD
  case PersonVD:
    if(status == 0){
      if(A._1 == -1)//own nothing
        return PersonVD(-1, 0, 1)
      else{
        return PersonVD(A._1, 0, 1)
        }
    }else if(status == 1){
      if(A._3 == -2) 
        return PersonVD(-1, 0, 1)
      else return 
        PersonVD(A._1, A._2 - A._3 + e, 2)
      }else if(status == 2){
        return PersonVD(-1, 0, 0)
    }

  case ObjectVD:
     return ObjectVD(A._1, A._2)

sendmsg :(EdgeTriplet[VD, ED]) ⇒ Iterator[(VertexId, A)]
     if(PersonVD.status == 1){
          if(PersonVD.assignObj == -1){
          //Not assign
               ObjectVD send A(ObjectVD.VertexId, edge.attr - price, 0) to PersonVD
          }
          else{
               if(PersonVD.assignObj==ObjectVD.VertexID && ObjectVD.ownerId != PersonVD.VertexId)
                  send A(0, 0, 2) to PersonVD
               else Iterator.empty
          }
     }//Bidding Phase1
     else if(PersonVD.status == 2){
          PersonVD send A(PersonVD.VertexId, bid, -3) to ObjectVD.VertexId == assignObj
          PersonVD send A(0, 0, -1) to itself
     }else{
           if(PersonVD.VertexId == ObjectVD.ownerId) send(ObjectVD.VertexId, 0, -2) to PersonVD
           else Iterator.empty
           PersonVD send A(-1, 0, -2) to itself

     }

mergemsg :(A, A) ⇒ A
     if(A._3 == -3){
         Find MAX A._2, return A(PersonVD.VertexId, A._2, 1)
     }
     if(A._3 == -1){
         //empty msg
         return A(0 ,0 ,-1)
     }
          if(A._3 == -2){
         Find A._1 MAX return A(A._1 max, 0, -2)
     }else{
         Find A(best object’s VertexId, best object’s price, second best object’s price )

     }
