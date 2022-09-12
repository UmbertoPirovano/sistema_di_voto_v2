package politics;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

class CandidateTest {

	@Test
	void testSetParty() {
		Candidate c = new Candidate("Mattia","Garavaglia");
		Party p = new Party("Gruppo1");
		c.setParty(p);
		
		assertEquals(p,c.getParty());
	}
	
	@Test
	void testEquals() {
		Party p = new Party("Gruppo1");
		Candidate c1 = new Candidate("Mattia","Garavaglia",p);
		Candidate c2 = new Candidate("Mattia", "Garavaglia", p);
		
		assertEquals(c1,c2);
	}
	
	@Test
	void testNotEquals() {
		Party p = new Party("Gruppo1");
		Candidate c1 = new Candidate("Mattia","Garavaglia",p);
		Candidate c2 = new Candidate("Umberto", "Pirovano", p);
		
		assertNotEquals(c1,c2);
	}
}
