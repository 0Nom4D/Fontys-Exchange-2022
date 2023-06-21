//
//  AddressGeocodingUITests.swift
//  AddressGeocodingUITests
//
//  Created by Nom4D on 29/03/2023.
//

import XCTest
import CoreLocation

final class AddressGeocodingUITests: XCTestCase {

    let app = XCUIApplication()

    override func setUpWithError() throws {
        continueAfterFailure = false
        app.launch()
    }

    override func tearDownWithError() throws {}

    func testMapViewer_MapView_shouldExists() {
        let map = app.maps.firstMatch
        XCTAssertTrue(map.waitForExistence(timeout: 5))
    }

    func testMapViewer_MapView_shouldMove() {
        let map = app.maps.firstMatch

        map.swipeLeft()
        map.swipeDown()
        map.swipeUp()
        map.swipeRight()
        XCTAssertTrue(map.exists)
    }

    func testLocationFinder_SearchBar_shouldAcceptText() {
        let searchBar = app.searchFields["6969 Cool St, Weedsport, NY 13166"]
        searchBar.tap()

        let aKey = app.keys["A"]
        aKey.tap()

        let lKey = app.keys["l"]
        lKey.tap()

        let eKey = app.keys["e"]
        eKey.tap()

        let dKey = app.keys["d"]
        dKey.tap()

        let searchButton = app.buttons["Search"]
        searchButton.tap()

        let results = app.collectionViews.firstMatch
        XCTAssertTrue(results.exists)
    }

    func testLocationFinder_SearchBar_shouldDeleteText() {
        let searchBar = app.searchFields["6969 Cool St, Weedsport, NY 13166"]
        searchBar.tap()

        let aKey = app.keys["A"]
        aKey.tap()

        let lKey = app.keys["l"]
        lKey.tap()

        let eKey = app.keys["e"]
        eKey.tap()

        let dKey = app.keys["d"]
        dKey.tap()

        let deleteKey = app.keys["delete"]
        deleteKey.tap()

        let searchButton = app.buttons["Search"]
        searchButton.tap()

        let results = app.collectionViews.firstMatch
        XCTAssertTrue(results.exists)
    }

    func testLocationFinder_ResultList_shouldClickOnResult() {
        let searchBar = app.searchFields["6969 Cool St, Weedsport, NY 13166"]
        searchBar.tap()

        let aKey = app.keys["A"]
        aKey.tap()

        let lKey = app.keys["l"]
        lKey.tap()

        let eKey = app.keys["e"]
        eKey.tap()

        let dKey = app.keys["d"]
        dKey.tap()

        let searchButton = app.buttons["Search"]
        searchButton.tap()

        let firstResult = app.collectionViews["bottomDrawer"].staticTexts["Åled, Halmstad, Sweden"]
        XCTAssertTrue(firstResult.exists)
        firstResult.tap()

        let closeButton = app.buttons["bottomDrawer"]
        XCTAssertTrue(closeButton.exists)
    }

    func testLocationFinder_RemindList_shouldStoreCliked() {
        let searchBar = app.searchFields["6969 Cool St, Weedsport, NY 13166"]
        searchBar.tap()

        let aKey = app.keys["A"]
        aKey.tap()

        let lKey = app.keys["l"]
        lKey.tap()

        let eKey = app.keys["e"]
        eKey.tap()

        let dKey = app.keys["d"]
        dKey.tap()

        let searchButton = app.buttons["Search"]
        searchButton.tap()

        let firstResult = app.collectionViews["bottomDrawer"].staticTexts["Åled, Halmstad, Sweden"]
        XCTAssertTrue(firstResult.exists)
        firstResult.tap()

        let closeButton = app.buttons["bottomDrawer"]
        XCTAssertTrue(closeButton.exists)
        closeButton.tap()

        let remindedResult = app.collectionViews["bottomDrawer"].staticTexts["Åled, Halmstad, Sweden"]
        XCTAssertTrue(remindedResult.exists)
    }
}
