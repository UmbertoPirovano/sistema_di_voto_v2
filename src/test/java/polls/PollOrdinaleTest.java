package polls;

import static org.junit.jupiter.api.Assertions.*;

import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.List;

import org.junit.jupiter.api.Test;

import politics.Party;
import politics.PoliticalEntity;
import polls.PollCategorico.VoteCategorico;

class PollOrdinaleTest {
	
	/**
	 * Testa il funzionamento del metodo addCandidate di PollOrdinale, che aggiunge una PolicalEntity al PollOrdinale.
	 */
	@Test
	void testAddCandidate() {
		Party p = new Party("Gruppo1");
		PollOrdinale poll = new PollOrdinale("Test", "Test add candidate", Timestamp.valueOf("2022-07-01 00:00:00"), Timestamp.valueOf("2022-07-02 00:00:00"));
		poll.addCandidate(p);
		
		List<PoliticalEntity> polEnt = poll.getCandidates();
		
		boolean found = false;
		
		for(PoliticalEntity pE: polEnt) {
			if(pE instanceof Party && pE.equals(p)) {
				found = true;
				break;
			}
		}
		
		assertTrue(found);
	}
	
	/**
	 * Testa il funzionamento del metodo vote di PollOrdinale, che restituisce un'istanza di Vote.
	 */
	@Test
	void testVote() {
		Party p = new Party("Gruppo1");
		PollOrdinale poll = new PollOrdinale("Test", "Test vote", Timestamp.valueOf("2022-07-01 00:00:00"), Timestamp.valueOf("2022-07-02 00:00:00"));
		poll.addCandidate(p);
		List<PoliticalEntity> polEnt = new ArrayList<>();
		polEnt.add(p);
		PollOrdinale.VoteOrdinale expected = poll.new VoteOrdinale(polEnt);
		Vote actual = poll.vote(polEnt);
		assertEquals(expected,actual);
	}

}
