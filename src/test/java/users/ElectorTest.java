package users;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

class ElectorTest {
	
	@Test
	public void testNotEquals() {
		Elector e1 = new Elector("mattia","mattia","Mattia","Garavaglia");
		Elector e2 = new Elector("umberto","umberto","Umberto","Pirovano");
		assertNotEquals(e1,e2);
	}
	
	@Test
	public void testEquals() {
		Elector e1 = new Elector("mattia","mattia","Mattia","Garavaglia");
		Elector e2 = new Elector("mattia","test","Mattia","Garavaglia");
		
		assertEquals(e1,e2);
	}

}
