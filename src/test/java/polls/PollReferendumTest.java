package polls;

import static org.junit.jupiter.api.Assertions.*;

import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.List;

import org.junit.jupiter.api.Test;

import politics.Party;
import politics.PoliticalEntity;

class PollReferendumTest {
	
	/**
	 * Testa il funzionamento del metodo vote di PollReferendum, che restituisce un'istanza di Vote.
	 */
	@Test
	void testVote() {
		PollReferendum poll = new PollReferendum("Test", "Test add candidate", Timestamp.valueOf("2022-07-01 00:00:00"), Timestamp.valueOf("2022-07-02 00:00:00"));
		List<PoliticalEntity> polEnt = new ArrayList<>();
		polEnt.add(new Party("Si'"));
		PollReferendum.VoteReferendum expected = poll.new VoteReferendum(true);
		Vote actual = poll.vote(polEnt);
		assertEquals(expected,actual);
	}

}
