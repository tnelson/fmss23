/*
  Validation for the simplified network model contained in basenet.als

  We'll start with: validation on a specific specialized network. In practice,
  there might be many such test networks, along with many property checks.
*/
open basenet

/* --------------------------------------------------------------------
SANITY CHECKS ON SPECIALIZED NETWORKS
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
   -- Table at m0:
   (m0.(n.forwardTables)).frows = (Self -> h -> j1)
   -- Table at m1: 
   (m1.(n.forwardTables)).frows = (j0 -> h -> j1)
   -- Table at m2:
   (m2.(n.forwardTables)).frows = (j0 -> h -> j1)
   -- Table at m3:
   (m3.(n.forwardTables)).frows = (j0 -> h -> Receive) 
}

-- TN TODO: what is the role of sndrIdent/rcvrIdent? (port ids, reused across nodes?)
--   (if so, can fill that context in comments on table settings above)

-- Ask Alloy to produce example instances containing this test network.
-- TASK: View how the various definitions of reachability vary for TestNet.
run TestNet for 1 but 
   4 Name, 2 LinkIdent, 3 Link, 3 NetHdr, 4 ForwardTable
