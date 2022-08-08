package gui;

import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;

/*MVC: questa classe rappresenta la classe View del pattern MVC in quanto si occupa di mostrare i dati
	all'utente e gestisce le interazioni con l'infrastuttura sottostante.*/

public class GuiApplication extends Application {

	@Override
	public void start(Stage primaryStage) throws Exception{
		//System.out.println(LoginWindowView.class.getResource("/main/resources/gui/LoginWindow.fxml"));
		Parent root = FXMLLoader.load(getClass().getResource("LoginWindow.fxml"));
		
		primaryStage.setTitle("Sistema di voto elettronico - Login");
		primaryStage.setScene(new Scene(root, 500, 390));
		primaryStage.setResizable(false);
		primaryStage.show();
	}
	
	/**
	* Lancia il metodo start.
	*/	
	public static void show() {
		launch();
	}
}
