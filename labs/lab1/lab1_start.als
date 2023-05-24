/* ====================================================================
A SIMPLIFIED MODEL OF NETWORK STATE 

  Adapted for use in lab 1, FMSS23
  Starter model and template
    for use _after_ the initial intro-to-reachability collab livecode

==================================================================== */
/* --------------------------------------------------------------------
TYPES
-------------------------------------------------------------------- */
open util/ordering [Name]               -- impose a totals ordering on Name

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
-- Four competing definitions of reachability in this model
   reachable1: NetHdr -> Name -> Name,
   reachable2: NetHdr -> Name -> Name,
   reachable3: NetHdr -> Name -> Name,
   reachable4: NetHdr -> Name -> Name
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
      reachable4 = {  h: NetHdr, m, m": Name | 
         some k, k": links, kin, kout: LinkIdent | 
            (m -> kout -> k) in outLinks
         && (m" -> kin -> k") in inLinks
         && (h -> kout) in Self.((m.forwardTables).frows)
         && (kin -> h) in ((m".forwardTables).frows).Receive
         && (  k = k" || (k -> k") in ^(h.oneStep)  )      }

}


/* --------------------------------------------------------------------
SANITY CHECKS ON SPECIALIZED NETWORKS

In practice, there might be many such test networks, along with many 
property checks. This template has been simplified for brevity.

-------------------------------------------------------------------- */
 
one sig m0, m1, m2, m3 extends Name {}
one sig k01, k12, k23 extends Link {}
one sig j0, j1 extends LinkIdent {}  
one sig h, h0, h1 extends NetHdr {}

-- This predicate describes a specific network topology with 4 members,
-- along with a specific packet trajectory
pred TestNet [n: NetworkState] {
   -- members of the network and which are endpoints
   n.members = m0 + m1 + m2 + m3 && n.users = m0 + m3
   -- topology of the network
   n.links = k01 + k12 + k23
   k01.sndr = m0      && k12.sndr = m1      && k23.sndr = m2
   k01.sndrIdent = j1 && k12.sndrIdent = j1 && k23.sndrIdent = j1
   k01.rcvr = m1      && k12.rcvr = m2      && k23.rcvr = m3
   k01.rcvrIdent = j0 && k12.rcvrIdent = j0 && k23.rcvrIdent = j0

   -- seeking a packet (with header h) from m0 to m3
   h.src = m0 && h.dst = m3

   -- specific forwarding table for this example network
   -- since this is for a single packet `h`, the table only covers `h`
   -- Table at m0: `h` received from OS, send out port j1
   (m0.(n.forwardTables)).frows = (Self -> h -> j1)
   -- Table at m1: `h` received from port `j0`, send out port `j1`
   (m1.(n.forwardTables)).frows = (j0 -> h -> j1)
   -- Table at m2: `h` received from port `j0`, send out port `j1`
   (m2.(n.forwardTables)).frows = (j0 -> h -> j1)
   -- Table at m3: `h` received from port `j0`, handled by OS
   (m3.(n.forwardTables)).frows = (j0 -> h -> Receive) 

   -- Impose the natural ordering; may be useful later
   lt [m0, m1] && lt [m1, m2] && lt [m2, m3]
}

-- ******************************************************************
-- ** TASK 1: Use the visualizer to examine how the various definitions 
--   of reachability vary for this test network. 
--   (1) Execute ---> "Run TestNet..."
--   (2) Click the "Instance" link in the pane to the right.
--       (Mac users may need to find and expand the visualization window)
--   (3) We have also provided an alternative, domain-specific visualization.
--       To access it, while viewing the default visualization:
--         (I) Click File->Export To->XML, and save the instance in a file.
--         (II) Open a web browser (that supports JavaScript) and go to:
--              https://tnelson.github.io/sterling-ts/
--         (III) In the lower-right corner, click "Manual Datum"
--         (IV) Click to add XML from file, and select the file you saved to.
--              You should see a directed graph appear.
--         (V) In the upper-right corner, click "Script"
--         (VI) We have pre-loaded the visualizer for this problem. Click the 
--              blue "Run" button at the top of the window.

run TestNet for 1 but 
   4 Name, 2 LinkIdent, 3 Link, 3 NetHdr, 4 ForwardTable

-- ******************************************************************
-- ** TASK 2: Write some behavioral predicates that might be useful.
-- **    (Recall these don't need to be true of every network.)
-- ** Write them *semi-formally*, in natural language, first. 
-- ** Then we'll fill in one formally together.





-- ******************************************************************
-- ** TASK 3: Write some assertions about TestNet
-- **    (Here, you'll want something true in every network. Hint, use implication!)
-- ** Write them *semi-formally*, in natural language, first. 
-- ** Then we'll fill in one formally together.





