package polls;

import java.util.Iterator;
import java.util.List;

import politics.PoliticalEntity;

public interface Vote {
	
	public Iterator<PoliticalEntity> getPreference();
}
