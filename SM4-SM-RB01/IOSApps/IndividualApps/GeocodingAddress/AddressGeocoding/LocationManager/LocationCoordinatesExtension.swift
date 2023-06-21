//
//  LocationCoordinatesExtension.swift
//  AddressGeocoding
//
//  Created by Nom4D on 27/03/2023.
//

import Foundation
import CoreLocation

extension CLLocationCoordinate2D: Equatable {
    public static func == (lhs: CLLocationCoordinate2D, rhs: CLLocationCoordinate2D) -> Bool {
        return lhs.latitude == rhs.latitude && lhs.longitude == rhs.longitude
    }
}
