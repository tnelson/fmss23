/* ====================================================================
A SIMPLIFIED MODEL OF NETWORK STATE 

  Adapted for use in lab 1, FMSS23

==================================================================== */
/* --------------------------------------------------------------------
TYPES
-------------------------------------------------------------------- */

sig Name { }                            -- the name of a network member
   
sig LinkIdent, SessionIdent { }
 
abstract sig Command { }
   one sig Receive, Drop extends Command { }
one sig Self { }

sig NetHdr
   {  src, dst: Name, sessionIdent: SessionIdent  }
fact NetHdrsAreRecords { all h, h": NetHdr |
   (  h.sessionIdent = h".sessionIdent 
   && h.src = h".src && h.dst = h".dst  ) 
   => h = h" }           -- if an object is a "record," the identity of
                        -- an instance depends only on its field values

sig Link { 
   sndr: Name, 
   sndrIdent: LinkIdent,
   rcvr: Name,
   rcvrIdent: LinkIdent
} 
-- Note that links are not records; there can be two distinct 
-- individuals that happen to have the same field values.
   
sig ForwardTable { frows:
   (LinkIdent + Self) -> NetHdr -> (LinkIdent + Command)  }

/* --------------------------------------------------------------------
NETWORK STATES
   There are many versions of reachable here, only one of which is
usable. For pedagogical purposes, the names must be obscured!
-------------------------------------------------------------------- */

sig NetworkState {
-- Network components (domain knowledge).
   members: set Name,        -- every member has at least a unique name
   disj infras, users: set members,    -- trusted and untrusted members
   links: set Link,
   outLinks, inLinks: members -> LinkIdent -> links,         -- derived
-- Network traffic (domain knowledge).
   sendTable: members -> NetHdr,
   receiveTable: members -> NetHdr,
-- Behavior of network members (specification).
   forwardTables: members -> lone ForwardTable,
   oneStep: NetHdr -> links -> links,              -- all derived below
   reachable1: NetHdr -> Name -> Name,
   reachable2: NetHdr -> Name -> Name,
   reachable3: NetHdr -> Name -> Name,
   endToEndReachable: NetHdr -> Name -> Name,
   reachable: NetHdr -> Name -> Name
}  {
-- Network topology.
   -- Each member is an infrastructure member or user.
      infras + users = members
   -- All links have at least one endpoint that is a member.
      all k: links | some ((k.sndr + k.rcvr) & members) 
   -- There are no self-links.
      all k: links | k.sndr != k.rcvr
   -- For each member, its local linkIdents are disjoint.
      all disj k0, k1: links | 
      (   (k0.sndr = k1.sndr => k0.sndrIdent != k1.sndrIdent)
      &&  (k0.rcvr = k1.rcvr => k0.rcvrIdent != k1.rcvrIdent)
      &&  (k0.sndr = k1.rcvr => k0.sndrIdent != k1.rcvrIdent)  )
   -- Derivation of inLinks and outLinks.
      outLinks = { m: members, i: LinkIdent, k: links |
         k.sndr = m && k.sndrIdent = i                }         
      inLinks = { m: members, i: LinkIdent, k: links |
         k.rcvr = m && k.rcvrIdent = i               }
-- Behavior of network members.  
   -- The forwardTable.  The absence of a matching table entry means 
   -- that an incoming packet is dropped.
      -- Consistency: All inLinks and outLinks are real.
      all m: members, kin: 
         (((m.forwardTables).frows).(LinkIdent + Command)).NetHdr |
         ( (m -> kin) in inLinks.links || kin in Self )
      all m: members, kout:
              NetHdr.((LinkIdent + Self).((m.forwardTables).frows)) |
         kout ! in Command => (m -> kout) in outLinks.links
      -- A forwardTable can yield multiple outLinks for replication for
      -- allCast service.  In addition to yielding multiple outLinks, 
      -- it can yield a Receive command.  Otherwise it is 
      -- deterministic.  If there is no matching entry for an incoming
      -- packet, it is dropped.
         all m: members, ki: LinkIdent + Command, h: NetHdr |
            (  lone h.(ki.((m.forwardTables).frows))
            || h.(ki.((m.forwardTables).frows)) in 
                  (LinkIdent + Receive)            )
-- Reachability.
      oneStep = {  h: NetHdr, disj k, k": links |
         some m: Name, kin, kout: LinkIdent |
            (m -> kin -> k) in inLinks 
         && (m -> kout -> k") in outLinks
         && (kin -> h -> kout) in (m.forwardTables).frows  }
      reachable1 = {  h: NetHdr, m, m": Name | 
         some k, k": links | 
            m in k.sndr && m" in k".rcvr && (k -> k") in ^(h.oneStep) }
      reachable2 = {  h: NetHdr, m, m": Name | 
         some k, k": links | 
            m in k.sndr && m" in k".rcvr 
         && (  k = k" || (k -> k") in ^(h.oneStep)  )          }
      reachable3 = {  h: NetHdr, m, m": Name | 
         some k, k": links, kin, kout: LinkIdent | 
            (m -> kout -> k) in outLinks
         && (m" -> kin -> k") in inLinks
         && (h -> kout) in 
               (LinkIdent + Self).((m.forwardTables).frows)
         && (kin -> h) in 
               ((m".forwardTables).frows).(LinkIdent + Receive)
         && (  k = k" || (k -> k") in ^(h.oneStep)  )                }
      endToEndReachable = {  h: NetHdr, m, m": Name | 
         some k, k": links, kin, kout: LinkIdent | 
            (m -> kout -> k) in outLinks
         && (m" -> kin -> k") in inLinks
         && (h -> kout) in Self.((m.forwardTables).frows)
         && (kin -> h) in ((m".forwardTables).frows).Receive
         && (  k = k" || (k -> k") in ^(h.oneStep)  )      }


      reachable = reachable3
      -- TN: TODO ^^^ which to default to? (does it matter, without the further predicates?)
}
